import Mathlib
import Rudin.PMA.Chapter04

/-!
# Chapter 5: Differentiation

Isolated preparation from the accepted nineteen-node inventory.
Proofs are assembled in inventory order; publication and production
integration are pending separate authorization.
-/


/- Assembly source: Chapter05OpeningDraft.lean -/

open Filter Set
open scoped Topology

noncomputable section

namespace Rudin.PMA.Chapter05

/-! ### PMA-5.1: Difference quotients and domain-relative derivatives. -/

def DifferenceQuotient (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (f t - f x) / (t - x)

def HasDomainDerivative (S : Set ℝ) (f : ℝ → ℝ) (x d : ℝ) : Prop :=
  x ∈ S ∧ Chapter04.FunctionLimitOn S (DifferenceQuotient f x) x d

def DomainDifferentiableAt (S : Set ℝ) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ d, HasDomainDerivative S f x d

def DomainDifferentiableOn (S A : Set ℝ) (f : ℝ → ℝ) : Prop :=
  A ⊆ S ∧ ∀ x ∈ A, DomainDifferentiableAt S f x

def HasRightDerivative (a b : ℝ) (f : ℝ → ℝ) (x d : ℝ) : Prop :=
  Chapter04.RightLimitOn a b (DifferenceQuotient f x) x d

def HasLeftDerivative (a b : ℝ) (f : ℝ → ℝ) (x d : ℝ) : Prop :=
  Chapter04.LeftLimitOn a b (DifferenceQuotient f x) x d

def pma5_1_contract : Prop :=
  (∀ S f x d, HasDomainDerivative S f x d ↔
    x ∈ S ∧ Chapter02.IsLimitPoint x S ∧ HasDerivWithinAt f d S x) ∧
  (∀ a b f x d, a < b → x ∈ Icc a b →
    (HasDomainDerivative (Icc a b) f x d ↔
      Chapter04.FunctionLimitOn (Ioo a b) (DifferenceQuotient f x) x d)) ∧
  (∀ a b f x d, x ∈ Ioo a b →
    (HasDomainDerivative (Icc a b) f x d ↔ HasDerivAt f d x)) ∧
  (∀ a b f d, a < b →
    (HasDomainDerivative (Icc a b) f a d ↔ HasRightDerivative a b f a d)) ∧
  (∀ a b f d, a < b →
    (HasDomainDerivative (Icc a b) f b d ↔ HasLeftDerivative a b f b d)) ∧
  (∀ a b f x d, a ≤ x → x < b →
    (HasRightDerivative a b f x d ↔ HasDerivWithinAt f d (Ici x) x)) ∧
  (∀ a b f x d, a < x → x ≤ b →
    (HasLeftDerivative a b f x d ↔ HasDerivWithinAt f d (Iic x) x)) ∧
  (∀ a b f x d, x ∈ Ioo a b →
    (HasDomainDerivative (Icc a b) f x d ↔
      HasLeftDerivative a b f x d ∧ HasRightDerivative a b f x d)) ∧
  (∀ S f x d e, HasDomainDerivative S f x d → HasDomainDerivative S f x e → d = e) ∧
  (∀ S f x, DomainDifferentiableAt S f x ↔ ∃! d, HasDomainDerivative S f x d) ∧
  (∀ a b f x, a < b → x ∈ Icc a b →
    (DomainDifferentiableAt (Icc a b) f x ↔ DifferentiableWithinAt ℝ f (Icc a b) x)) ∧
  (∀ a b A f, a < b →
    (DomainDifferentiableOn (Icc a b) A f ↔
      A ⊆ Icc a b ∧ ∀ x ∈ A, DifferentiableWithinAt ℝ f (Icc a b) x)) ∧
  (∀ a b f x d, a < b → x ∈ Icc a b → HasDomainDerivative (Icc a b) f x d →
    derivWithin f (Icc a b) x = d) ∧
  (∀ a b f, ¬ DomainDifferentiableAt (Ioo a b) f a ∧
    ¬ DomainDifferentiableAt (Ioo a b) f b)

/-! ### PMA-5.2: Differentiability implies continuity on the domain. -/

def pma5_2_contract : Prop :=
  ∀ S f x, DomainDifferentiableAt S f x → Chapter04.FunctionContinuousWithinAt S f x

/-! ### PMA-5.3: Arithmetic, with a locally restricted quotient domain. -/

def QuotientDomain (S : Set ℝ) (g : ℝ → ℝ) : Set ℝ := S ∩ {t | g t ≠ 0}

def pma5_3_contract : Prop :=
  ∀ S f g x df dg, HasDomainDerivative S f x df → HasDomainDerivative S g x dg →
    HasDomainDerivative S (fun t => f t + g t) x (df + dg) ∧
    HasDomainDerivative S (fun t => f t * g t) x (df * g x + f x * dg) ∧
    (g x ≠ 0 →
      (𝓝[QuotientDomain S g \ {x}] x = 𝓝[S \ {x}] x) ∧
      HasDomainDerivative (QuotientDomain S g) (fun t => f t / g t) x
        ((g x * df - f x * dg) / (g x)^2))

/-! ### PMA-5.4: Constants, identity, integer powers, polynomials and rational functions. -/

def IntegerPowerDomain (n : ℤ) : Set ℝ := {x | x ≠ 0 ∨ 0 ≤ n}

def pma5_4_contract : Prop :=
  (∀ c x : ℝ, HasDomainDerivative univ (fun _ => c) x 0) ∧
  (∀ x : ℝ, HasDomainDerivative univ (fun t => t) x 1) ∧
  (∀ n : ℤ, ∀ x ∈ IntegerPowerDomain n,
    HasDomainDerivative (IntegerPowerDomain n) (fun t => t ^ n) x
      ((n : ℝ) * x ^ (n - 1))) ∧
  (∀ x : ℝ, HasDomainDerivative univ (fun t : ℝ => t ^ (0 : ℤ)) x 0) ∧
  (∀ p : Polynomial ℝ, ∀ x : ℝ,
    HasDomainDerivative univ (fun t => p.eval t) x (p.derivative.eval x)) ∧
  (∀ p q : Polynomial ℝ, ∀ x : ℝ, q.eval x ≠ 0 →
    HasDomainDerivative {t | q.eval t ≠ 0} (fun t => p.eval t / q.eval t) x
      ((q.eval x * p.derivative.eval x - p.eval x * q.derivative.eval x) /
        (q.eval x)^2))

/-! ### PMA-5.5: Chain rule with the outer function defined on a containing interval. -/

def pma5_5_contract : Prop :=
  ∀ (a b : ℝ) (J : Set ℝ) (f g : ℝ → ℝ) (x df dg : ℝ),
    a < b → x ∈ Icc a b → OrdConnected J →
    Chapter04.FunctionContinuousOn (Icc a b) f → MapsTo f (Icc a b) J →
    HasDomainDerivative (Icc a b) f x df → HasDomainDerivative J g (f x) dg →
    HasDomainDerivative (Icc a b) (g ∘ f) x (dg * df)

theorem differenceQuotient_eq_slope (f : ℝ → ℝ) (x : ℝ) :
    DifferenceQuotient f x = slope f x := by
  funext t
  exact (slope_def_field f x t).symm

theorem hasDomainDerivative_iff (S : Set ℝ) (f : ℝ → ℝ) (x d : ℝ) :
    HasDomainDerivative S f x d ↔
      x ∈ S ∧ Chapter02.IsLimitPoint x S ∧ HasDerivWithinAt f d S x := by
  constructor
  · rintro ⟨hx, hlim⟩
    refine ⟨hx, hlim.1, hasDerivWithinAt_iff_tendsto_slope.mpr ?_⟩
    simpa only [differenceQuotient_eq_slope] using
      (Chapter04.functionLimitOn_iff_tendsto S _ x d hlim.1).mp hlim
  · rintro ⟨hx, hacc, hd⟩
    refine ⟨hx, (Chapter04.functionLimitOn_iff_tendsto S _ x d hacc).mpr ?_⟩
    simpa only [differenceQuotient_eq_slope] using
      hasDerivWithinAt_iff_tendsto_slope.mp hd

theorem closedInterval_limitPoint {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    Chapter02.IsLimitPoint x (Icc a b) :=
  (Chapter02.isLimitPoint_iff_accPt x (Icc a b)).mpr
    ((uniqueDiffOn_Icc hab x hx).accPt)

theorem hasDomainDerivative_Icc_iff {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (f : ℝ → ℝ) (d : ℝ) :
    HasDomainDerivative (Icc a b) f x d ↔ HasDerivWithinAt f d (Icc a b) x := by
  rw [hasDomainDerivative_iff]
  simp only [hx, closedInterval_limitPoint hab hx, true_and]

theorem interval_punctured_Ioo_eq_Icc {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    𝓝[Ioo a b \ {x}] x = 𝓝[Icc a b \ {x}] x := by
  have hmem : Ioo a b ∈ 𝓝[Icc a b \ {x}] x := by
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with rfl | rfl | hx'
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hab)] with t ht htb
      have hta : t ≠ x := by simpa only [mem_singleton_iff] using ht.2
      exact ⟨lt_of_le_of_ne ht.1.1 hta.symm, htb⟩
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds hab)] with t ht hat
      have htb : t ≠ x := by simpa only [mem_singleton_iff] using ht.2
      exact ⟨hat, lt_of_le_of_ne ht.1.2 htb⟩
    · exact nhdsWithin_le_nhds (Ioo_mem_nhds hx'.1 hx'.2)
  have heq : Ioo a b ∩ (Icc a b \ {x}) = Ioo a b \ {x} := by
    ext t
    simp only [mem_inter_iff, Set.mem_sdiff, mem_Ioo, mem_Icc, mem_singleton_iff]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, ⟨⟨h.1.1.le, h.1.2.le⟩, h.2⟩⟩
  simpa only [heq] using nhdsWithin_inter_of_mem hmem

theorem closedInterval_source_derivative_iff {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Icc a b) (f : ℝ → ℝ) (d : ℝ) :
    HasDomainDerivative (Icc a b) f x d ↔
      Chapter04.FunctionLimitOn (Ioo a b) (DifferenceQuotient f x) x d := by
  have hacc := closedInterval_limitPoint hab hx
  have ha : Chapter02.IsLimitPoint x (Ioo a b) := by
    rw [Chapter04.functionLimitPoint_iff_neBot, interval_punctured_Ioo_eq_Icc hab hx]
    exact (Chapter04.functionLimitPoint_iff_neBot _ _).mp hacc
  simp only [HasDomainDerivative, hx, true_and,
    Chapter04.functionLimitOn_iff_tendsto _ _ _ _ hacc,
    Chapter04.functionLimitOn_iff_tendsto _ _ _ _ ha,
    interval_punctured_Ioo_eq_Icc hab hx]

theorem hasDomainDerivative_interior_iff {a b x : ℝ} (hx : x ∈ Ioo a b)
    (f : ℝ → ℝ) (d : ℝ) :
    HasDomainDerivative (Icc a b) f x d ↔ HasDerivAt f d x := by
  rw [hasDomainDerivative_Icc_iff (hx.1.trans hx.2) (Ioo_subset_Icc_self hx)]
  exact ⟨fun h => h.hasDerivAt (Icc_mem_nhds hx.1 hx.2), fun h => h.hasDerivWithinAt⟩

theorem hasRightDerivative_iff {a b x : ℝ} (hax : a ≤ x) (hxb : x < b)
    (f : ℝ → ℝ) (d : ℝ) :
    HasRightDerivative a b f x d ↔ HasDerivWithinAt f d (Ici x) x := by
  simp only [HasRightDerivative, Chapter04.RightLimitOn, hax, hxb, true_and,
    nhdsWithin_Ioo_eq_nhdsGT hxb]
  rw [← hasDerivWithinAt_Ioi_iff_Ici,
    hasDerivWithinAt_iff_tendsto_slope' (show x ∉ Ioi x by simp)]
  rw [differenceQuotient_eq_slope]

theorem hasLeftDerivative_iff {a b x : ℝ} (hax : a < x) (hxb : x ≤ b)
    (f : ℝ → ℝ) (d : ℝ) :
    HasLeftDerivative a b f x d ↔ HasDerivWithinAt f d (Iic x) x := by
  simp only [HasLeftDerivative, Chapter04.LeftLimitOn, hax, hxb, true_and,
    nhdsWithin_Ioo_eq_nhdsLT hax]
  rw [← hasDerivWithinAt_Iio_iff_Iic,
    hasDerivWithinAt_iff_tendsto_slope' (show x ∉ Iio x by simp)]
  rw [differenceQuotient_eq_slope]

theorem hasDomainDerivative_leftEndpoint_iff {a b : ℝ} (hab : a < b)
    (f : ℝ → ℝ) (d : ℝ) :
    HasDomainDerivative (Icc a b) f a d ↔ HasRightDerivative a b f a d := by
  rw [hasDomainDerivative_Icc_iff hab (left_mem_Icc.mpr hab.le),
    hasRightDerivative_iff le_rfl hab]
  simp only [HasDerivWithinAt, nhdsWithin_Icc_eq_nhdsGE hab]

theorem hasDomainDerivative_rightEndpoint_iff {a b : ℝ} (hab : a < b)
    (f : ℝ → ℝ) (d : ℝ) :
    HasDomainDerivative (Icc a b) f b d ↔ HasLeftDerivative a b f b d := by
  rw [hasDomainDerivative_Icc_iff hab (right_mem_Icc.mpr hab.le),
    hasLeftDerivative_iff hab le_rfl]
  simp only [HasDerivWithinAt, nhdsWithin_Icc_eq_nhdsLE hab]

theorem hasDomainDerivative_iff_sides {a b x : ℝ} (hx : x ∈ Ioo a b)
    (f : ℝ → ℝ) (d : ℝ) :
    HasDomainDerivative (Icc a b) f x d ↔
      HasLeftDerivative a b f x d ∧ HasRightDerivative a b f x d := by
  rw [closedInterval_source_derivative_iff (hx.1.trans hx.2) (Ioo_subset_Icc_self hx)]
  exact Chapter04.interval_limit_iff_sides _ _ hx

theorem hasDomainDerivative_unique {S : Set ℝ} {f : ℝ → ℝ} {x d e : ℝ}
    (hd : HasDomainDerivative S f x d) (he : HasDomainDerivative S f x e) : d = e :=
  Chapter04.functionLimitOn_unique S (DifferenceQuotient f x) x d e hd.2 he.2

theorem domainDifferentiableAt_iff_existsUnique (S : Set ℝ) (f : ℝ → ℝ) (x : ℝ) :
    DomainDifferentiableAt S f x ↔ ∃! d, HasDomainDerivative S f x d := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, hd, fun e he => hasDomainDerivative_unique he hd⟩
  · rintro ⟨d, hd, _⟩
    exact ⟨d, hd⟩

theorem domainDifferentiableAt_Icc_iff {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Icc a b) (f : ℝ → ℝ) :
    DomainDifferentiableAt (Icc a b) f x ↔ DifferentiableWithinAt ℝ f (Icc a b) x := by
  constructor
  · rintro ⟨d, hd⟩
    exact ((hasDomainDerivative_Icc_iff hab hx f d).mp hd).differentiableWithinAt
  · intro hf
    exact ⟨derivWithin f (Icc a b) x,
      (hasDomainDerivative_Icc_iff hab hx f _).mpr hf.hasDerivWithinAt⟩

theorem domainDifferentiableOn_Icc_iff {a b : ℝ} (hab : a < b)
    (A : Set ℝ) (f : ℝ → ℝ) :
    DomainDifferentiableOn (Icc a b) A f ↔
      A ⊆ Icc a b ∧ ∀ x ∈ A, DifferentiableWithinAt ℝ f (Icc a b) x := by
  constructor
  · rintro ⟨hsub, hf⟩
    exact ⟨hsub, fun x hx => (domainDifferentiableAt_Icc_iff hab (hsub hx) f).mp (hf x hx)⟩
  · rintro ⟨hsub, hf⟩
    exact ⟨hsub, fun x hx => (domainDifferentiableAt_Icc_iff hab (hsub hx) f).mpr (hf x hx)⟩

theorem pma5_1 : pma5_1_contract := by
  refine ⟨hasDomainDerivative_iff,
    fun a b f x d hab hx => closedInterval_source_derivative_iff hab hx f d,
    fun a b f x d hx => hasDomainDerivative_interior_iff hx f d,
    fun a b f d hab => hasDomainDerivative_leftEndpoint_iff hab f d,
    fun a b f d hab => hasDomainDerivative_rightEndpoint_iff hab f d,
    fun a b f x d hax hxb => hasRightDerivative_iff hax hxb f d,
    fun a b f x d hax hxb => hasLeftDerivative_iff hax hxb f d,
    fun a b f x d hx => hasDomainDerivative_iff_sides hx f d,
    fun S f x d e hd he => hasDomainDerivative_unique hd he,
    domainDifferentiableAt_iff_existsUnique,
    fun a b f x hab hx => domainDifferentiableAt_Icc_iff hab hx f,
    fun a b A f hab => domainDifferentiableOn_Icc_iff hab A f,
    ?_, ?_⟩
  · intro a b f x d hab hx hd
    exact ((hasDomainDerivative_Icc_iff hab hx f d).mp hd).derivWithin
      (uniqueDiffOn_Icc hab x hx)
  · intro a b f
    constructor
    · rintro ⟨d, hd⟩
      exact (lt_irrefl a) hd.1.1
    · rintro ⟨d, hd⟩
      exact (lt_irrefl b) hd.1.2

theorem pma5_2 : pma5_2_contract := by
  rintro S f x ⟨d, hd⟩
  have hf := (hasDomainDerivative_iff S f x d).mp hd
  exact (Chapter04.functionContinuousWithinAt_iff S f x hf.1).mpr
    hf.2.2.continuousWithinAt

theorem quotientDomain_punctured_nhds {S : Set ℝ} {g : ℝ → ℝ} {x dg : ℝ}
    (hg : HasDerivWithinAt g dg S x) (hne : g x ≠ 0) :
    𝓝[QuotientDomain S g \ {x}] x = 𝓝[S \ {x}] x := by
  have hmem : {t | g t ≠ 0} ∈ 𝓝[S \ {x}] x :=
    (hg.continuousWithinAt.tendsto.eventually_ne hne).filter_mono
      (nhdsWithin_mono _ sdiff_subset)
  have heq : QuotientDomain S g \ {x} = (S \ {x}) ∩ {t | g t ≠ 0} := by
    ext t
    simp only [QuotientDomain, Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq,
      mem_singleton_iff]
    tauto
  rw [heq]
  exact nhdsWithin_inter_of_mem' hmem

theorem pma5_3 : pma5_3_contract := by
  intro S f g x df dg hf hg
  have hdf := (hasDomainDerivative_iff S f x df).mp hf
  have hdg := (hasDomainDerivative_iff S g x dg).mp hg
  refine ⟨(hasDomainDerivative_iff S _ x _).mpr ⟨hdf.1, hdf.2.1, hdf.2.2.fun_add hdg.2.2⟩,
    (hasDomainDerivative_iff S _ x _).mpr ⟨hdf.1, hdf.2.1, hdf.2.2.fun_mul hdg.2.2⟩, ?_⟩
  intro hne
  have hfilter := quotientDomain_punctured_nhds hdg.2.2 hne
  refine ⟨hfilter, (hasDomainDerivative_iff (QuotientDomain S g) _ x _).mpr
    ⟨⟨hdf.1, hne⟩, ?_, ?_⟩⟩
  · rw [Chapter04.functionLimitPoint_iff_neBot, hfilter]
    exact (Chapter04.functionLimitPoint_iff_neBot S x).mp hdf.2.1
  · have hd := (hdf.2.2.fun_div hdg.2.2 hne).mono
      (show QuotientDomain S g ⊆ S from inter_subset_left)
    simpa only [mul_comm df (g x)] using hd

theorem hasDomainDerivative_univ_iff (f : ℝ → ℝ) (x d : ℝ) :
    HasDomainDerivative univ f x d ↔ HasDerivAt f d x := by
  have hacc : Chapter02.IsLimitPoint x (univ : Set ℝ) :=
    (Chapter02.isLimitPoint_iff_accPt x univ).mpr
      (uniqueDiffWithinAt_univ (𝕜 := ℝ) (x := x)).accPt
  rw [hasDomainDerivative_iff]
  simp only [mem_univ, hacc, true_and, hasDerivWithinAt_univ]

theorem hasDomainDerivative_of_hasDerivAt {S : Set ℝ} (hS : IsOpen S)
    {f : ℝ → ℝ} {x d : ℝ} (hx : x ∈ S) (hf : HasDerivAt f d x) :
    HasDomainDerivative S f x d := by
  apply (hasDomainDerivative_iff S f x d).mpr
  exact ⟨hx, (Chapter02.isLimitPoint_iff_accPt x S).mpr
    (hS.uniqueDiffWithinAt (𝕜 := ℝ) hx).accPt, hf.hasDerivWithinAt⟩

theorem integerPowerDomain_isOpen (n : ℤ) : IsOpen (IntegerPowerDomain n) := by
  by_cases hn : 0 ≤ n
  · have h : IntegerPowerDomain n = univ := by
      ext x
      simp only [IntegerPowerDomain, mem_ofPred_eq, mem_univ, hn, or_true]
    rw [h]
    exact isOpen_univ
  · have h : IntegerPowerDomain n = ({0} : Set ℝ)ᶜ := by
      ext x
      simp only [IntegerPowerDomain, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff,
        hn, or_false]
    rw [h]
    exact isOpen_compl_singleton

theorem pma5_4 : pma5_4_contract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c x
    exact (hasDomainDerivative_univ_iff _ x 0).mpr (hasDerivAt_const x c)
  · intro x
    exact (hasDomainDerivative_univ_iff _ x 1).mpr (hasDerivAt_id x)
  · intro n x hx
    exact hasDomainDerivative_of_hasDerivAt (integerPowerDomain_isOpen n) hx
      (hasDerivAt_zpow n x hx)
  · intro x
    apply (hasDomainDerivative_univ_iff _ x 0).mpr
    simpa only [zpow_zero] using hasDerivAt_const x (1 : ℝ)
  · intro p x
    exact (hasDomainDerivative_univ_iff _ x _).mpr (p.hasDerivAt x)
  · intro p q x hq
    have hp' := (hasDomainDerivative_univ_iff _ x _).mpr (p.hasDerivAt x)
    have hq' := (hasDomainDerivative_univ_iff _ x _).mpr (q.hasDerivAt x)
    have hd := (pma5_3 univ (fun t => p.eval t) (fun t => q.eval t)
      x (p.derivative.eval x) (q.derivative.eval x) hp' hq').2.2 hq
    simpa only [QuotientDomain, univ_inter] using hd.2

theorem pma5_5 : pma5_5_contract := by
  intro a b J f g x df dg _hab _hx _hJ _hcont hmaps hf hg
  have hdf := (hasDomainDerivative_iff (Icc a b) f x df).mp hf
  have hdg := (hasDomainDerivative_iff J g (f x) dg).mp hg
  exact (hasDomainDerivative_iff (Icc a b) (g ∘ f) x (dg * df)).mpr
    ⟨hdf.1, hdf.2.1, hdg.2.2.comp x hdf.2.2 hmaps⟩

end Rudin.PMA.Chapter05


/- Assembly source: Chapter05OscillationDraft.lean -/

open Set Filter
open scoped Topology

namespace Rudin.PMA.Chapter05

noncomputable section

/-! ### PMA-5.6: Two oscillatory examples -/

/-- The totalized reciprocal formula has the required zero extension. -/
def OscillationLinear (x : ℝ) : ℝ := x * Real.sin (1 / x)

/-- The totalized reciprocal formula has the required zero extension. -/
def OscillationQuadratic (x : ℝ) : ℝ := x ^ 2 * Real.sin (1 / x)

def pma5_6_contract : Prop :=
  OscillationLinear 0 = 0 ∧
  Continuous OscillationLinear ∧
  (∀ x : ℝ, x ≠ 0 → HasDerivAt OscillationLinear
    (Real.sin (1 / x) - Real.cos (1 / x) / x) x) ∧
  ¬ DifferentiableAt ℝ OscillationLinear 0 ∧
  OscillationQuadratic 0 = 0 ∧
  Differentiable ℝ OscillationQuadratic ∧
  HasDerivAt OscillationQuadratic 0 0 ∧
  (∀ x : ℝ, x ≠ 0 → HasDerivAt OscillationQuadratic
    (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x) ∧
  ¬ ContinuousAt (deriv OscillationQuadratic) 0

theorem oscillationLinear_zero : OscillationLinear 0 = 0 := by
  simp [OscillationLinear]

theorem oscillationQuadratic_zero : OscillationQuadratic 0 = 0 := by
  simp [OscillationQuadratic]

theorem oscillationLinear_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt OscillationLinear
      (Real.sin (1 / x) - Real.cos (1 / x) / x) x := by
  unfold OscillationLinear
  simp only [one_div]
  apply ((hasDerivAt_id x).mul (hasDerivAt_inv hx).sin).congr_deriv
  simp only [id_eq, one_mul]
  field_simp
  ring

theorem oscillationQuadratic_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt OscillationQuadratic
      (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
  unfold OscillationQuadratic
  simp only [one_div]
  apply (((hasDerivAt_id x).pow 2).mul (hasDerivAt_inv hx).sin).congr_deriv
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp
  ring

theorem oscillationLinear_abs_le (x : ℝ) : |OscillationLinear x| ≤ |x| := by
  rw [OscillationLinear, abs_mul]
  calc
    |x| * |Real.sin (1 / x)| ≤ |x| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
    _ = |x| := mul_one _

theorem oscillationLinear_continuousAt_zero : ContinuousAt OscillationLinear 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx
  rw [oscillationLinear_zero, Real.dist_eq, sub_zero]
  exact (oscillationLinear_abs_le x).trans_lt (by simpa [Real.dist_eq] using hx)

theorem oscillationLinear_continuous : Continuous OscillationLinear := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact oscillationLinear_continuousAt_zero
  · exact (oscillationLinear_hasDerivAt hx).continuousAt

theorem oscillationLinear_slope (x : ℝ) :
    slope OscillationLinear 0 x = Chapter04.OscillatingSine x := by
  by_cases hx : x = 0
  · simp [hx, Chapter04.OscillatingSine]
  · simp [slope_def_field, OscillationLinear, Chapter04.OscillatingSine, hx,
      one_div, mul_div_cancel_left₀]

theorem oscillationLinear_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ OscillationLinear 0 := by
  intro hd
  apply Chapter04.oscillatingSine_no_side_limit true
  refine ⟨deriv OscillationLinear 0, ?_⟩
  have h := hd.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  rw [show slope OscillationLinear 0 = Chapter04.OscillatingSine from
    funext oscillationLinear_slope] at h
  exact h

theorem oscillationQuadratic_slope (x : ℝ) :
    slope OscillationQuadratic 0 x = OscillationLinear x := by
  by_cases hx : x = 0
  · simp [hx, OscillationLinear]
  · rw [slope_def_field]
    simp only [OscillationQuadratic, OscillationLinear, zero_pow (by decide : 2 ≠ 0),
      zero_mul, sub_zero]
    field_simp

theorem oscillationQuadratic_hasDerivAt_zero : HasDerivAt OscillationQuadratic 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  rw [show slope OscillationQuadratic 0 = OscillationLinear from
    funext oscillationQuadratic_slope]
  simpa only [oscillationLinear_zero] using
    oscillationLinear_continuousAt_zero.tendsto.mono_left nhdsWithin_le_nhds

theorem oscillationQuadratic_differentiable : Differentiable ℝ OscillationQuadratic := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact oscillationQuadratic_hasDerivAt_zero.differentiableAt
  · exact (oscillationQuadratic_hasDerivAt hx).differentiableAt

theorem oscillationQuadratic_deriv_attains_neg_one_near_zero {b : ℝ} (hb : 0 < b) :
    ∃ x ∈ Ioo 0 b, deriv OscillationQuadratic x = -1 := by
  have hp : 0 < 2 * Real.pi := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (b⁻¹ / (2 * Real.pi))
  have hphase : b⁻¹ < (n : ℝ) * (2 * Real.pi) := (div_lt_iff₀ hp).mp hn
  have hphasepos : 0 < (n : ℝ) * (2 * Real.pi) := (inv_pos.mpr hb).trans hphase
  refine ⟨((n : ℝ) * (2 * Real.pi))⁻¹,
    ⟨inv_pos.mpr hphasepos, ?_⟩, ?_⟩
  · simpa only [inv_inv] using
      (inv_lt_inv₀ hphasepos (inv_pos.mpr hb)).mpr hphase
  · have hsin : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
      simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 n
    simpa only [one_div, inv_inv, hsin, Real.cos_nat_mul_two_pi, mul_zero, zero_sub] using
      (oscillationQuadratic_hasDerivAt (ne_of_gt (inv_pos.mpr hphasepos))).deriv

theorem oscillationQuadratic_deriv_not_continuousAt_zero :
    ¬ ContinuousAt (deriv OscillationQuadratic) 0 := by
  intro hc
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  obtain ⟨x, hx, hdx⟩ := oscillationQuadratic_deriv_attains_neg_one_near_zero hδ
  have hdist : dist x 0 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hx.1] using hx.2
  have hbad := hclose hdist
  rw [hdx, oscillationQuadratic_hasDerivAt_zero.deriv] at hbad
  norm_num [Real.dist_eq] at hbad

theorem pma5_6 : pma5_6_contract :=
  ⟨oscillationLinear_zero, oscillationLinear_continuous,
    fun _ hx => oscillationLinear_hasDerivAt hx,
    oscillationLinear_not_differentiableAt_zero,
    oscillationQuadratic_zero, oscillationQuadratic_differentiable,
    oscillationQuadratic_hasDerivAt_zero,
    fun _ hx => oscillationQuadratic_hasDerivAt hx,
    oscillationQuadratic_deriv_not_continuousAt_zero⟩

/-- Boundary probe: the off-zero derivative formula must not be extended to zero. -/
theorem oscillationQuadratic_offZero_formula_wrong_at_zero :
    deriv OscillationQuadratic 0 ≠
      2 * (0 : ℝ) * Real.sin (1 / 0) - Real.cos (1 / 0) := by
  rw [oscillationQuadratic_hasDerivAt_zero.deriv]
  norm_num


end

end Rudin.PMA.Chapter05


/- Assembly source: Chapter05MiddleDraft.lean -/

noncomputable section
open Set Filter Topology

namespace Rudin.PMA.Chapter05

/-! ### PMA-5.7: Local extrema in a metric space -/

def MetricLocalMaximum {X : Type*} [MetricSpace X] (f : X → ℝ) (p : X) : Prop :=
  ∃ δ > 0, ∀ q, dist p q < δ → f q ≤ f p

def MetricLocalMinimum {X : Type*} [MetricSpace X] (f : X → ℝ) (p : X) : Prop :=
  ∃ δ > 0, ∀ q, dist p q < δ → f p ≤ f q

def pma5_7_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X] (f : X → ℝ) (p : X),
    (MetricLocalMaximum f p ↔ IsLocalMax f p) ∧
    (MetricLocalMinimum f p ↔ IsLocalMin f p)

theorem pma5_7 : pma5_7_contract := by
  intro X _ f p
  constructor
  · change (∃ δ > 0, ∀ q, dist p q < δ → f q ≤ f p) ↔
      ∀ᶠ q in 𝓝 p, f q ≤ f p
    rw [Metric.eventually_nhds_iff]
    simp only [dist_comm]
  · change (∃ δ > 0, ∀ q, dist p q < δ → f p ≤ f q) ↔
      ∀ᶠ q in 𝓝 p, f p ≤ f q
    rw [Metric.eventually_nhds_iff]
    simp only [dist_comm]

/-! ### PMA-5.8: The derivative at an interior local extremum -/

def pma5_8_contract : Prop :=
  ∀ (f : ℝ → ℝ) (a b x d : ℝ), x ∈ Ioo a b →
    HasDerivWithinAt f d (Icc a b) x →
    (IsLocalMaxOn f (Icc a b) x ∨ IsLocalMinOn f (Icc a b) x) → d = 0

theorem pma5_8 : pma5_8_contract := by
  intro f a b x d hx hd he
  have hn : Icc a b ∈ 𝓝 x := mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Ioo_subset_Icc_self
  rcases he with he | he
  · exact (he.isLocalMax hn).hasDerivAt_eq_zero (hd.hasDerivAt hn)
  · exact (he.isLocalMin hn).hasDerivAt_eq_zero (hd.hasDerivAt hn)

/-! ### PMA-5.9: Cauchy's mean value theorem -/

def pma5_9_contract : Prop :=
  ∀ (f g f' g' : ℝ → ℝ) (a b : ℝ), a < b →
    ContinuousOn f (Icc a b) → ContinuousOn g (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) →
    (∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) →
    ∃ x ∈ Ioo a b, (f b - f a) * g' x = (g b - g a) * f' x

theorem pma5_9 : pma5_9_contract := by
  intro f g f' g' a b hab hfc hgc hfd hgd
  obtain ⟨x, hx, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hfd g g' hgc hgd
  exact ⟨x, hx, he.symm⟩

/-! ### PMA-5.10: The real mean value theorem -/

def pma5_10_contract : Prop :=
  ∀ (f f' : ℝ → ℝ) (a b : ℝ), a < b →
    ContinuousOn f (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) →
    ∃ x ∈ Ioo a b, f b - f a = (b - a) * f' x

theorem pma5_10 : pma5_10_contract := by
  intro f f' a b hab hfc hfd
  obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f' hab hfc hfd
  refine ⟨x, hx, ?_⟩
  rw [he, mul_div_cancel₀ _ (sub_ne_zero.mpr hab.ne')]

/-! ### PMA-5.11: Derivative signs and monotonicity on an open interval -/

def pma5_11_contract : Prop :=
  ∀ (f f' : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) →
    ((∀ x ∈ Ioo a b, 0 ≤ f' x) → MonotoneOn f (Ioo a b)) ∧
    ((∀ x ∈ Ioo a b, f' x = 0) → ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, f x = f y) ∧
    ((∀ x ∈ Ioo a b, f' x ≤ 0) → AntitoneOn f (Ioo a b))

theorem pma5_11 : pma5_11_contract := by
  intro f f' a b _ hf
  have hc : ContinuousOn f (Ioo a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ interior (Ioo a b), HasDerivWithinAt f (f' x) (interior (Ioo a b)) x := by
    intro x hx
    exact (hf x (interior_subset hx)).hasDerivWithinAt
  have hm : (∀ x ∈ Ioo a b, 0 ≤ f' x) → MonotoneOn f (Ioo a b) := fun h =>
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo a b) hc hd
      (fun x hx => h x (interior_subset hx))
  have ha : (∀ x ∈ Ioo a b, f' x ≤ 0) → AntitoneOn f (Ioo a b) := fun h =>
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo a b) hc hd
      (fun x hx => h x (interior_subset hx))
  refine ⟨hm, ?_, ha⟩
  intro hz x hx y hy
  have hm' := hm (fun z hz' => (hz z hz').ge)
  have ha' := ha (fun z hz' => (hz z hz').le)
  rcases le_total x y with hxy | hyx
  · exact le_antisymm (hm' hx hy hxy) (ha' hx hy hxy)
  · exact le_antisymm (ha' hy hx hyx) (hm' hy hx hyx)

/-! ### PMA-5.12: Darboux's theorem and absence of simple derivative discontinuities -/

def pma5_12_contract : Prop :=
  ∀ (f f' : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) →
    (∀ m, ((f' a < m ∧ m < f' b) ∨ (f' b < m ∧ m < f' a)) →
      ∃ x ∈ Ioo a b, f' x = m) ∧
    (∀ x l, Chapter04.LeftLimitOn a b f' x l → l = f' x) ∧
    (∀ x r, Chapter04.RightLimitOn a b f' x r → r = f' x) ∧
    (∀ x, ¬ Chapter04.FirstKindDiscontinuityOn a b f' x)

theorem derivative_leftLimit_eq {f f' : ℝ → ℝ} {a b x l : ℝ}
    (hf : ∀ y ∈ Icc a b, HasDerivWithinAt f (f' y) (Icc a b) y)
    (hl : Chapter04.LeftLimitOn a b f' x l) : l = f' x := by
  have hsub : Ioo a x ⊆ Icc a b := fun y hy => ⟨hy.1.le, hy.2.le.trans hl.2.1⟩
  have hd : DifferentiableOn ℝ f (Ioo a x) := fun y hy =>
    ((hf y (hsub hy)).mono hsub).differentiableWithinAt
  have hc : ContinuousWithinAt f (Ioo a x) x :=
    (hf x ⟨hl.1.le, hl.2.1⟩).continuousWithinAt.mono hsub
  have he : f' =ᶠ[𝓝[<] x] deriv f := by
    filter_upwards [Ioo_mem_nhdsLT hl.1] with y hy
    exact ((hf y (hsub hy)).hasDerivAt
      (mem_of_superset (Ioo_mem_nhds hy.1 (hy.2.trans_le hl.2.1)) Ioo_subset_Icc_self)).deriv.symm
  have ht : Tendsto f' (𝓝[<] x) (𝓝 l) := by
    simpa only [nhdsWithin_Ioo_eq_nhdsLT hl.1] using hl.2.2
  have hdl := hasDerivWithinAt_Iic_of_tendsto_deriv hd hc (Ioo_mem_nhdsLT hl.1) (ht.congr' he)
  have hdl' : HasDerivWithinAt f l (Icc a x) x := hdl.mono Icc_subset_Iic_self
  have hdf' : HasDerivWithinAt f (f' x) (Icc a x) x :=
    (hf x ⟨hl.1.le, hl.2.1⟩).mono (Icc_subset_Icc le_rfl hl.2.1)
  exact (uniqueDiffOn_Icc hl.1 x ⟨hl.1.le, le_rfl⟩).eq_deriv _ hdl' hdf'

theorem derivative_rightLimit_eq {f f' : ℝ → ℝ} {a b x r : ℝ}
    (hf : ∀ y ∈ Icc a b, HasDerivWithinAt f (f' y) (Icc a b) y)
    (hr : Chapter04.RightLimitOn a b f' x r) : r = f' x := by
  have hsub : Ioo x b ⊆ Icc a b := fun y hy => ⟨hr.1.trans hy.1.le, hy.2.le⟩
  have hd : DifferentiableOn ℝ f (Ioo x b) := fun y hy =>
    ((hf y (hsub hy)).mono hsub).differentiableWithinAt
  have hc : ContinuousWithinAt f (Ioo x b) x :=
    (hf x ⟨hr.1, hr.2.1.le⟩).continuousWithinAt.mono hsub
  have he : f' =ᶠ[𝓝[>] x] deriv f := by
    filter_upwards [Ioo_mem_nhdsGT hr.2.1] with y hy
    exact ((hf y (hsub hy)).hasDerivAt
      (mem_of_superset (Ioo_mem_nhds (hr.1.trans_lt hy.1) hy.2) Ioo_subset_Icc_self)).deriv.symm
  have ht : Tendsto f' (𝓝[>] x) (𝓝 r) := by
    simpa only [nhdsWithin_Ioo_eq_nhdsGT hr.2.1] using hr.2.2
  have hdr := hasDerivWithinAt_Ici_of_tendsto_deriv hd hc (Ioo_mem_nhdsGT hr.2.1) (ht.congr' he)
  have hdr' : HasDerivWithinAt f r (Icc x b) x := hdr.mono Icc_subset_Ici_self
  have hdf' : HasDerivWithinAt f (f' x) (Icc x b) x :=
    (hf x ⟨hr.1, hr.2.1.le⟩).mono (Icc_subset_Icc hr.1 le_rfl)
  exact (uniqueDiffOn_Icc hr.2.1 x ⟨le_rfl, hr.2.1.le⟩).eq_deriv _ hdr' hdf'

theorem pma5_12 : pma5_12_contract := by
  intro f f' a b hab hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    rcases hm with ⟨ham, hmb⟩ | ⟨hbm, hma⟩
    · exact exists_hasDerivWithinAt_eq_of_gt_of_lt hab.le hf ham hmb
    · exact exists_hasDerivWithinAt_eq_of_lt_of_gt hab.le hf hma hbm
  · intro x l hl
    exact derivative_leftLimit_eq hf hl
  · intro x r hr
    exact derivative_rightLimit_eq hf hr
  · intro x hx
    obtain ⟨l, hl⟩ := hx.2.2.1
    obtain ⟨r, hr⟩ := hx.2.2.2
    exact hx.2.1 ((Chapter04.continuous_iff_oneSided_eq f' hx.1 hl hr).mpr
      ⟨derivative_leftLimit_eq hf hl, derivative_rightLimit_eq hf hr⟩)

/-! Boundary probes: interior extremum is essential, and a one-sided endpoint
derivative need not be a two-sided derivative of the chosen total extension. -/

theorem middle_probe_endpoint_fermat_failure :
    HasDerivWithinAt (fun x : ℝ => x) 1 (Icc 0 1) 0 ∧
    IsLocalMinOn (fun x : ℝ => x) (Icc 0 1) 0 ∧ (1 : ℝ) ≠ 0 := by
  refine ⟨hasDerivWithinAt_id 0 _, ?_, one_ne_zero⟩
  change ∀ᶠ x in 𝓝[Icc (0 : ℝ) 1] 0, 0 ≤ x
  filter_upwards [self_mem_nhdsWithin] with x hx using hx.1

theorem middle_probe_oneSided_abs :
    (∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt abs 1 (Icc 0 1) x) ∧
    ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
  refine ⟨?_, not_differentiableAt_abs_zero⟩
  intro x hx
  exact (hasDerivWithinAt_id x (Icc 0 1)).congr_of_mem
    (fun y hy => abs_of_nonneg hy.1) hx

theorem middle_probe_MVT_without_endpoint_differentiability :
    (∃ x ∈ Ioo (0 : ℝ) 1, |(1 : ℝ)| - |(0 : ℝ)| = (1 - 0) * (1 : ℝ)) ∧
    ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
  refine ⟨pma5_10 abs (fun _ => 1) 0 1 zero_lt_one continuous_abs.continuousOn ?_,
    not_differentiableAt_abs_zero⟩
  exact fun x hx => hasDerivAt_abs_pos hx.1

end Rudin.PMA.Chapter05


/- Assembly source: Chapter05LHopitalDraft.lean -/

noncomputable section
open Set Filter
open scoped Topology

namespace Rudin.PMA.Chapter05

/-! ### PMA-5.13: L'Hopital at every finite or infinite interval endpoint. -/

/-- The four possible approaches to an endpoint of a nondegenerate real interval,
including both infinite endpoints. The derivative assumptions below need hold only
eventually on the approach, so every finite or extended interval is included. -/
inductive EndpointApproach where
  | right (a : ℝ)
  | left (b : ℝ)
  | positiveInfinity
  | negativeInfinity

def EndpointApproach.filter : EndpointApproach → Filter ℝ
  | .right a => 𝓝[>] a
  | .left b => 𝓝[<] b
  | .positiveInfinity => atTop
  | .negativeInfinity => atBot

/-- An extended-real target for an ordinary real-valued function. -/
def EndpointLimit (e : EndpointApproach) (f : ℝ → ℝ) (A : EReal) : Prop :=
  Tendsto (fun x => (f x : EReal)) e.filter (𝓝 A)

/-- Full local endpoint form of PMA 5.13. In the infinite-denominator branches
there is no hypothesis on the numerator's limit. Eventual nonvanishing is a
conclusion, so the quotient's source domain is respected. -/
def pma5_13_contract : Prop :=
  ∀ (e : EndpointApproach) (f f' g g' : ℝ → ℝ) (A : EReal),
    (∀ᶠ x in e.filter, HasDerivAt f (f' x) x) →
    (∀ᶠ x in e.filter, HasDerivAt g (g' x) x) →
    (∀ᶠ x in e.filter, g' x ≠ 0) →
    EndpointLimit e (fun x => f' x / g' x) A →
    ((EndpointLimit e f 0 ∧ EndpointLimit e g 0) ∨
      EndpointLimit e g ⊤ ∨ EndpointLimit e g ⊥) →
    (∀ᶠ x in e.filter, g x ≠ 0) ∧ EndpointLimit e (fun x => f x / g x) A

theorem EndpointApproach.neBot (e : EndpointApproach) : e.filter.NeBot := by
  cases e <;> dsimp [EndpointApproach.filter] <;> infer_instance

theorem EndpointApproach.exists_convex_mem_subset (e : EndpointApproach)
    {s : Set ℝ} (hs : s ∈ e.filter) :
    ∃ t ∈ e.filter, Convex ℝ t ∧ t ⊆ s := by
  cases e with
  | right a =>
    obtain ⟨b, hab, hb⟩ := (nhdsGT_basis a).mem_iff.mp hs
    exact ⟨Ioo a b, (nhdsGT_basis a).mem_of_mem hab, convex_Ioo a b, hb⟩
  | left b =>
    obtain ⟨a, hab, ha⟩ := (nhdsLT_basis b).mem_iff.mp hs
    exact ⟨Ioo a b, (nhdsLT_basis b).mem_of_mem hab, convex_Ioo a b, ha⟩
  | positiveInfinity =>
    obtain ⟨a, _, ha⟩ := atTop_basis_Ioi.mem_iff.mp hs
    exact ⟨Ioi a, atTop_basis_Ioi.mem_of_mem trivial, convex_Ioi a, ha⟩
  | negativeInfinity =>
    obtain ⟨b, _, hb⟩ := atBot_basis_Iio.mem_iff.mp hs
    exact ⟨Iio b, atBot_basis_Iio.mem_of_mem trivial, convex_Iio b, hb⟩

/-- Cauchy MVT on a convex real domain, with an arbitrary ordering of the two
points. This form avoids assuming a sign for the derivative of the denominator. -/
theorem ratio_mvt_on_convex {s : Set ℝ} (hs : Convex ℝ s)
    {f f' g g' : ℝ → ℝ}
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ s, HasDerivAt g (g' x) x)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    ∃ c ∈ s, (g x - g y) * f' c = (f x - f y) * g' c := by
  have hc : s.OrdConnected := convex_iff_ordConnected.mp hs
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hsub : Icc x y ⊆ s := hc.out hx hy
    obtain ⟨c, hcm, heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hxy
      (fun z hz => (hf z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => hf z (hsub (Ioo_subset_Icc_self hz))) g g'
      (fun z hz => (hg z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => hg z (hsub (Ioo_subset_Icc_self hz)))
    exact ⟨c, hsub (Ioo_subset_Icc_self hcm), by nlinarith [heq]⟩
  · have hsub : Icc y x ⊆ s := hc.out hy hx
    obtain ⟨c, hcm, heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hyx
      (fun z hz => (hf z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => hf z (hsub (Ioo_subset_Icc_self hz))) g g'
      (fun z hz => (hg z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => hg z (hsub (Ioo_subset_Icc_self hz)))
    exact ⟨c, hsub (Ioo_subset_Icc_self hcm), heq⟩

/-- A derivative-ratio lower bound gives an anchored function-ratio lower bound. -/
theorem ratio_lower_bound_on_convex {s : Set ℝ} (hs : Convex ℝ s)
    {f f' g g' : ℝ → ℝ} {v x y : ℝ}
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z)
    (hg : ∀ z ∈ s, HasDerivAt g (g' z) z)
    (hg' : ∀ z ∈ s, g' z ≠ 0)
    (hr : ∀ z ∈ s, v < f' z / g' z)
    (hx : x ∈ s) (hy : y ∈ s) (hgyx : g y < g x) (hgx : 0 < g x) :
    v + (f y - v * g y) / g x < f x / g x := by
  have hne : x ≠ y := by intro h; subst x; exact (lt_irrefl _ hgyx)
  obtain ⟨c, hc, heq⟩ := ratio_mvt_on_convex hs hf hg hx hy hne
  have hd : g x - g y ≠ 0 := ne_of_gt (sub_pos.mpr hgyx)
  have hratio : (f x - f y) / (g x - g y) = f' c / g' c := by
    apply (div_eq_div_iff hd (hg' c hc)).mpr
    nlinarith [heq]
  have hlt : v * (g x - g y) < f x - f y :=
    (lt_div_iff₀ (sub_pos.mpr hgyx)).mp (hratio.symm ▸ hr c hc)
  apply (lt_div_iff₀ hgx).mpr
  rw [add_mul, div_mul_cancel₀ _ hgx.ne']
  nlinarith

theorem endpoint_ratio_eventually_gt (e : EndpointApproach)
    {f f' g g' : ℝ → ℝ} {r v : ℝ}
    (hf : ∀ᶠ x in e.filter, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in e.filter, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in e.filter, g' x ≠ 0)
    (hginf : Tendsto g e.filter atTop)
    (hratio : ∀ᶠ x in e.filter, v < f' x / g' x) (hrv : r < v) :
    ∀ᶠ x in e.filter, r < f x / g x := by
  have : e.filter.NeBot := e.neBot
  obtain ⟨s, hs, hconv, hsub⟩ := e.exists_convex_mem_subset (hf.and (hg.and (hg'.and hratio)))
  obtain ⟨y, hy⟩ := Filter.nonempty_of_mem hs
  have hinv : Tendsto (fun x => (g x)⁻¹) e.filter (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hginf
  have hdiv : Tendsto (fun x => (f y - v * g y) / g x) e.filter (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := f y - v * g y)).mul hinv
  have hbound : Tendsto (fun x => v + (f y - v * g y) / g x) e.filter (𝓝 v) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := v)).add hdiv
  filter_upwards [hs, hginf.eventually (eventually_gt_atTop (max 0 (g y))),
    hbound.eventually (lt_mem_nhds hrv)] with x hx hgx hbx
  exact hbx.trans (ratio_lower_bound_on_convex hconv
    (fun z hz => (hsub hz).1) (fun z hz => (hsub hz).2.1)
    (fun z hz => (hsub hz).2.2.1) (fun z hz => (hsub hz).2.2.2)
    hx hy (lt_of_le_of_lt (le_max_right _ _) hgx)
    (lt_of_le_of_lt (le_max_left _ _) hgx))

theorem endpoint_ratio_eventually_lt (e : EndpointApproach)
    {f f' g g' : ℝ → ℝ} {r v : ℝ}
    (hf : ∀ᶠ x in e.filter, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in e.filter, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in e.filter, g' x ≠ 0)
    (hginf : Tendsto g e.filter atTop)
    (hratio : ∀ᶠ x in e.filter, f' x / g' x < v) (hvr : v < r) :
    ∀ᶠ x in e.filter, f x / g x < r := by
  have h := endpoint_ratio_eventually_gt e (f := fun x => -f x)
    (f' := fun x => -f' x) (g := g) (g' := g')
    (hf.mono fun x hx => hx.neg) hg hg' hginf
    (hratio.mono fun x hx => by simpa only [neg_div, neg_lt_neg_iff] using hx)
    (neg_lt_neg hvr)
  simpa only [neg_div, neg_lt_neg_iff] using h

/-- Infinite-denominator l'Hopital with positive denominator divergence and an
arbitrary extended target. No limit or boundedness of the numerator is assumed. -/
theorem endpoint_lhopital_denominator_top (e : EndpointApproach)
    {f f' g g' : ℝ → ℝ} {A : EReal}
    (hf : ∀ᶠ x in e.filter, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in e.filter, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in e.filter, g' x ≠ 0)
    (hginf : Tendsto g e.filter atTop)
    (hratio : EndpointLimit e (fun x => f' x / g' x) A) :
    EndpointLimit e (fun x => f x / g x) A := by
  induction A using EReal.rec with
  | bot =>
    apply EReal.tendsto_coe_nhds_bot_iff.mpr
    apply tendsto_atBot.2
    intro r
    have hr := (EReal.tendsto_coe_nhds_bot_iff.mp hratio).eventually
      (eventually_lt_atBot (r - 1))
    exact (endpoint_ratio_eventually_lt e hf hg hg' hginf hr (by linarith)).mono
      (fun _ h => h.le)
  | coe a =>
    apply EReal.tendsto_coe.mpr
    have hr := EReal.tendsto_coe.mp hratio
    apply tendsto_order.2
    constructor
    · intro r hra
      obtain ⟨v, hrv, hva⟩ := exists_between hra
      exact endpoint_ratio_eventually_gt e hf hg hg' hginf
        (hr.eventually (lt_mem_nhds hva)) hrv
    · intro r har
      obtain ⟨v, hav, hvr⟩ := exists_between har
      exact endpoint_ratio_eventually_lt e hf hg hg' hginf
        (hr.eventually (gt_mem_nhds hav)) hvr
  | top =>
    apply EReal.tendsto_coe_nhds_top_iff.mpr
    apply tendsto_atTop.2
    intro r
    have hr := (EReal.tendsto_coe_nhds_top_iff.mp hratio).eventually
      (eventually_gt_atTop (r + 1))
    exact (endpoint_ratio_eventually_gt e hf hg hg' hginf hr (by linarith)).mono
      (fun _ h => h.le)

theorem endpoint_lhopital_zero_filter (e : EndpointApproach)
    {f f' g g' : ℝ → ℝ} {L : Filter ℝ}
    (hf : ∀ᶠ x in e.filter, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in e.filter, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in e.filter, g' x ≠ 0)
    (hfzero : Tendsto f e.filter (𝓝 0))
    (hgzero : Tendsto g e.filter (𝓝 0))
    (hratio : Tendsto (fun x => f' x / g' x) e.filter L) :
    Tendsto (fun x => f x / g x) e.filter L := by
  cases e with
  | right a => exact HasDerivAt.lhopital_zero_nhdsGT hf hg hg' hfzero hgzero hratio
  | left b => exact HasDerivAt.lhopital_zero_nhdsLT hf hg hg' hfzero hgzero hratio
  | positiveInfinity => exact HasDerivAt.lhopital_zero_atTop hf hg hg' hfzero hgzero hratio
  | negativeInfinity => exact HasDerivAt.lhopital_zero_atBot hf hg hg' hfzero hgzero hratio

/-- The denominator in the zero/zero branch is eventually nonzero. Applying
the zero/zero theorem to g/g gives limit one, which excludes any zero tail values. -/
theorem endpoint_zero_denominator_eventually_ne (e : EndpointApproach)
    {g g' : ℝ → ℝ}
    (hg : ∀ᶠ x in e.filter, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in e.filter, g' x ≠ 0)
    (hgzero : Tendsto g e.filter (𝓝 0)) :
    ∀ᶠ x in e.filter, g x ≠ 0 := by
  have hderiv : Tendsto (fun x => g' x / g' x) e.filter (𝓝 1) :=
    tendsto_const_nhds.congr' (hg'.mono fun x hx => (div_self hx).symm)
  have hlim := endpoint_lhopital_zero_filter e hg hg hg' hgzero hgzero hderiv
  have hn := hlim.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hn] with x hx
  intro hzero
  simp [hzero] at hx

theorem pma5_13 : pma5_13_contract := by
  intro e f f' g g' A hf hg hg' hratio hform
  rcases hform with ⟨hfzero, hgzero⟩ | hgtop | hgbot
  · have hf0 : Tendsto f e.filter (𝓝 0) := EReal.tendsto_coe.mp hfzero
    have hg0 : Tendsto g e.filter (𝓝 0) := EReal.tendsto_coe.mp hgzero
    refine ⟨endpoint_zero_denominator_eventually_ne e hg hg' hg0, ?_⟩
    change Tendsto ((fun x : ℝ => (x : EReal)) ∘ (fun x => f x / g x)) e.filter (𝓝 A)
    apply tendsto_comap_iff.mp
    apply endpoint_lhopital_zero_filter e hf hg hg' hf0 hg0
    exact tendsto_comap_iff.mpr hratio
  · have hgtend := EReal.tendsto_coe_nhds_top_iff.mp hgtop
    refine ⟨?_, endpoint_lhopital_denominator_top e hf hg hg' hgtend hratio⟩
    exact (hgtend.eventually (eventually_gt_atTop 0)).mono fun x hx => ne_of_gt hx
  · have hgneg := tendsto_neg_atBot_atTop.comp (EReal.tendsto_coe_nhds_bot_iff.mp hgbot)
    refine ⟨?_, ?_⟩
    · exact ((EReal.tendsto_coe_nhds_bot_iff.mp hgbot).eventually
        (eventually_lt_atBot 0)).mono fun x hx => ne_of_lt hx
    · have h := endpoint_lhopital_denominator_top e
        (f := fun x => -f x) (f' := fun x => -f' x)
        (g := fun x => -g x) (g' := fun x => -g' x)
        (hf.mono fun x hx => hx.neg) (hg.mono fun x hx => hx.neg)
        (hg'.mono fun x hx => neg_ne_zero.mpr hx) hgneg
        (by simpa only [neg_div_neg_eq] using hratio)
      simpa only [neg_div_neg_eq] using h

/-- The real trace of extended neighborhoods at positive infinity. -/
theorem lhopital_comap_top :
    Filter.comap (fun x : ℝ => (x : EReal)) (𝓝 ⊤) = atTop := by
  apply le_antisymm
  · have h : Tendsto (fun x : ℝ => (x : EReal))
        (Filter.comap (fun x : ℝ => (x : EReal)) (𝓝 ⊤)) (𝓝 ⊤) := tendsto_comap
    exact Filter.tendsto_id'.mp (EReal.tendsto_coe_nhds_top_iff.mp h)
  · exact EReal.tendsto_coe_atTop.le_comap

/-- The real trace of extended neighborhoods at negative infinity. -/
theorem lhopital_comap_bot :
    Filter.comap (fun x : ℝ => (x : EReal)) (𝓝 ⊥) = atBot := by
  apply le_antisymm
  · have h : Tendsto (fun x : ℝ => (x : EReal))
        (Filter.comap (fun x : ℝ => (x : EReal)) (𝓝 ⊥)) (𝓝 ⊥) := tendsto_comap
    exact Filter.tendsto_id'.mp (EReal.tendsto_coe_nhds_bot_iff.mp h)
  · exact EReal.tendsto_coe_atBot.le_comap

theorem lhopital_approach_top {s : Set ℝ} (hs : s ∈ (atTop : Filter ℝ)) :
    Chapter04.ExtendedApproachFilter s ⊤ = atTop := by
  have hset : {t : ℝ | (t : EReal) ≠ ⊤} = Set.univ := by ext t; simp
  rw [Chapter04.ExtendedApproachFilter, hset, Set.inter_univ, lhopital_comap_top]
  exact inf_eq_left.mpr (Filter.le_principal_iff.mpr hs)

theorem lhopital_approach_bot {s : Set ℝ} (hs : s ∈ (atBot : Filter ℝ)) :
    Chapter04.ExtendedApproachFilter s ⊥ = atBot := by
  have hset : {t : ℝ | (t : EReal) ≠ ⊥} = Set.univ := by ext t; simp
  rw [Chapter04.ExtendedApproachFilter, hset, Set.inter_univ, lhopital_comap_bot]
  exact inf_eq_left.mpr (Filter.le_principal_iff.mpr hs)

theorem lhopital_approach_Ioo_left {a b : ℝ} (hab : a < b) :
    Chapter04.ExtendedApproachFilter (Ioo a b) (a : EReal) = (.right a : EndpointApproach).filter := by
  rw [Chapter04.extendedApproachFilter_coe]
  have hs : Ioo a b \ {a} = Ioo a b := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_Ioo]
    exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h.1⟩⟩
  rw [hs, nhdsWithin_Ioo_eq_nhdsGT hab]
  rfl

theorem lhopital_approach_Ioo_right {a b : ℝ} (hab : a < b) :
    Chapter04.ExtendedApproachFilter (Ioo a b) (b : EReal) = (.left b : EndpointApproach).filter := by
  rw [Chapter04.extendedApproachFilter_coe]
  have hs : Ioo a b \ {b} = Ioo a b := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_Ioo]
    exact ⟨fun h => h.1, fun h => ⟨h, ne_of_lt h.2⟩⟩
  rw [hs, nhdsWithin_Ioo_eq_nhdsLT hab]
  rfl

theorem lhopital_approach_Ioi_left (a : ℝ) :
    Chapter04.ExtendedApproachFilter (Ioi a) (a : EReal) = (.right a : EndpointApproach).filter := by
  rw [Chapter04.extendedApproachFilter_coe]
  have hs : Ioi a \ {a} = Ioi a := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
  rw [hs]
  rfl

theorem lhopital_approach_Iio_right (b : ℝ) :
    Chapter04.ExtendedApproachFilter (Iio b) (b : EReal) = (.left b : EndpointApproach).filter := by
  rw [Chapter04.extendedApproachFilter_coe]
  have hs : Iio b \ {b} = Iio b := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_Iio]
    exact ⟨fun h => h.1, fun h => ⟨h, ne_of_lt h⟩⟩
  rw [hs]
  rfl

/-- Source-domain form, using exactly Chapter 4's nonvacuous extended limits.
The preceding filter identities instantiate this with Ioo, Ioi, Iio, or the
whole real line, covering every choice of finite or infinite interval endpoints. -/
theorem pma5_13_source_interval (s : Set ℝ) (c : EReal) (e : EndpointApproach)
    (he : Chapter04.ExtendedApproachFilter s c = e.filter)
    (f f' g g' : ℝ → ℝ) (A : EReal)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ s, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ s, g' x ≠ 0)
    (hratio : Chapter04.ExtendedLimitOn s (fun x => f' x / g' x) c A)
    (hform : (Chapter04.ExtendedLimitOn s f c 0 ∧ Chapter04.ExtendedLimitOn s g c 0) ∨
      Chapter04.ExtendedLimitOn s g c ⊤ ∨ Chapter04.ExtendedLimitOn s g c ⊥) :
    (∀ᶠ x in Chapter04.ExtendedApproachFilter s c, g x ≠ 0) ∧
      Chapter04.ExtendedLimitOn s (fun x => f x / g x) c A := by
  have hs : ∀ᶠ x in e.filter, x ∈ s := by
    change s ∈ e.filter
    rw [← he]
    have hle : Chapter04.ExtendedApproachFilter s c ≤ 𝓟 s :=
      inf_le_right.trans (Filter.principal_mono.mpr Set.inter_subset_left)
    exact hle (by simp)
  have hlimit : ∀ (h : ℝ → ℝ) (B : EReal),
      Chapter04.ExtendedLimitOn s h c B → EndpointLimit e h B := by
    intro h B hh
    simpa only [EndpointLimit, he] using
      (Chapter04.extendedLimitOn_iff_tendsto s h c B).mp hh |>.2
  have hforms : (EndpointLimit e f 0 ∧ EndpointLimit e g 0) ∨
      EndpointLimit e g ⊤ ∨ EndpointLimit e g ⊥ := by
    rcases hform with ⟨h1, h2⟩ | htop | hbot
    · exact Or.inl ⟨hlimit f 0 h1, hlimit g 0 h2⟩
    · exact Or.inr (Or.inl (hlimit g ⊤ htop))
    · exact Or.inr (Or.inr (hlimit g ⊥ hbot))
  obtain ⟨hne, hlim⟩ := pma5_13 e f f' g g' A
    (hs.mono fun x hx => hf x hx) (hs.mono fun x hx => hg x hx)
    (hs.mono fun x hx => hg' x hx) (hlimit _ A hratio) hforms
  refine ⟨by simpa only [he] using hne, ?_⟩
  apply (Chapter04.extendedLimitOn_iff_tendsto s _ c A).mpr
  exact ⟨by simpa only [he] using e.neBot,
    by simpa only [EndpointLimit, he] using hlim⟩


end Rudin.PMA.Chapter05

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names rawName _ => do
    let userName := privateToUserName rawName.eraseMacroScopes
    return if (`Rudin.PMA.Chapter05).isPrefixOf userName then names.push rawName else names
  if names.isEmpty then throwError "No Chapter 5 declarations found."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    if !forbidden.isEmpty then
      throwError "Forbidden axioms in {name}: {forbidden}"
  logInfo m!"PMA 5.13 draft audit: {names.size} declarations; only propext, Classical.choice, Quot.sound."


/- Assembly source: Chapter05TaylorDraft.lean -/

noncomputable section

open Set Filter
open scoped Topology Nat ContDiff

namespace Rudin.PMA.Chapter05

/-! ### PMA-5.14 — Actual existence of higher derivatives -/

/-- Existence is additional to the library's totalized derivative value. A successor derivative
requires its predecessor to exist throughout a relative neighborhood and to be differentiable
at the point. Relative neighborhoods retain the interval's one-sided endpoint convention. -/
def HigherExistsWithin (f : ℝ → ℝ) (s : Set ℝ) : ℕ → ℝ → Prop
  | 0, _ => True
  | k + 1, x =>
      (∀ᶠ y in 𝓝[s] x, HigherExistsWithin f s k y) ∧
      DifferentiableWithinAt ℝ (iteratedDerivWithin k f s) s x

def pma5_14_contract : Prop :=
  (∀ (f : ℝ → ℝ) (s : Set ℝ), iteratedDerivWithin 0 f s = f) ∧
  (∀ (f : ℝ → ℝ) (s : Set ℝ) (k : ℕ),
    iteratedDerivWithin (k + 1) f s = derivWithin (iteratedDerivWithin k f s) s) ∧
  (∀ (f : ℝ → ℝ) (s : Set ℝ) (k : ℕ) (x : ℝ),
    HigherExistsWithin f s (k + 1) x ↔
      (∀ᶠ y in 𝓝[s] x, HigherExistsWithin f s k y) ∧
      DifferentiableWithinAt ℝ (iteratedDerivWithin k f s) s x) ∧
  (∀ (f : ℝ → ℝ) (s : Set ℝ) (n k : ℕ) (x : ℝ),
    x ∈ s → k ≤ n → HigherExistsWithin f s n x → HigherExistsWithin f s k x)

theorem HigherExistsWithin.predecessor {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {x : ℝ}
    (h : HigherExistsWithin f s (n + 1) x) (hx : x ∈ s) :
    HigherExistsWithin f s n x :=
  h.1.self_of_nhdsWithin hx

theorem HigherExistsWithin.lower {f : ℝ → ℝ} {s : Set ℝ} {n k : ℕ} {x : ℝ}
    (h : HigherExistsWithin f s n x) (hx : x ∈ s) (hkn : k ≤ n) :
    HigherExistsWithin f s k x := by
  induction n with
  | zero => simpa only [Nat.le_zero.mp hkn] using h
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hkn with heq | hlt
    · simpa only [heq] using h
    · exact ih (h.predecessor hx) (Nat.lt_succ_iff.mp hlt)

theorem pma5_14 : pma5_14_contract := by
  refine ⟨fun _ _ => iteratedDerivWithin_zero, fun _ _ _ => iteratedDerivWithin_succ,
    fun _ _ _ _ => Iff.rfl, ?_⟩
  intro f s n k x hx hk h
  exact h.lower hx hk

/-! ### PMA-5.15 — Taylor's theorem under the source differentiability hypotheses -/

/-- The derivatives that occur in the hypothesis must actually exist; only the highest
predecessor is explicitly assumed continuous. No continuity is assumed of the nth derivative. -/
def TaylorHypotheses (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : Prop :=
  (∀ x ∈ Icc a b, HigherExistsWithin f (Icc a b) (n - 1) x) ∧
  ContinuousOn (iteratedDerivWithin (n - 1) f (Icc a b)) (Icc a b) ∧
  (∀ x ∈ Ioo a b, HigherExistsWithin f (Icc a b) n x)

def TaylorPolynomialValue (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (α β : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, iteratedDerivWithin k f (Icc a b) α * (β - α) ^ k / k !

def pma5_15_contract : Prop :=
  (∀ (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (α β : ℝ),
    a < b → 1 ≤ n → TaylorHypotheses f a b n → α ∈ Icc a b → β ∈ Icc a b →
    α ≠ β → ∃ x ∈ uIoo α β,
      f β = TaylorPolynomialValue f a b n α β +
        iteratedDerivWithin n f (Icc a b) x * (β - α) ^ n / n !) ∧
  (∀ (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (α β M : ℝ),
    a < b → 1 ≤ n → TaylorHypotheses f a b n → α ∈ Icc a b → β ∈ Icc a b →
    α ≠ β → (∀ x ∈ uIoo α β, |iteratedDerivWithin n f (Icc a b) x| ≤ M) →
    |f β - TaylorPolynomialValue f a b n α β| ≤ M * |β - α| ^ n / n !) ∧
  (∀ (f : ℝ → ℝ) (a b α β : ℝ),
    a < b → TaylorHypotheses f a b 1 → α ∈ Icc a b → β ∈ Icc a b → α ≠ β →
    ∃ x ∈ uIoo α β, f β - f α = (β - α) * derivWithin f (Icc a b) x)

theorem higherExists_contDiffOn {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ}
    (hex : ∀ x ∈ s, HigherExistsWithin f s n x)
    (hcont : ContinuousOn (iteratedDerivWithin n f s) s) :
    ContDiffOn ℝ n f s := by
  apply contDiffOn_of_continuousOn_differentiableOn_deriv
  · intro k hk
    have hkn : k ≤ n := by exact_mod_cast hk
    rcases Nat.eq_or_lt_of_le hkn with heq | hlt
    · simpa only [heq] using hcont
    · intro x hx
      exact ((hex x hx).lower hx (Nat.succ_le_of_lt hlt)).2.continuousWithinAt
  · intro k hk x hx
    have hkn : k < n := by exact_mod_cast hk
    exact ((hex x hx).lower hx (Nat.succ_le_of_lt hkn)).2

theorem iteratedDerivWithin_subset_of_contDiff {f : ℝ → ℝ} {s t : Set ℝ}
    {N k : ℕ} (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hf : ContDiffOn ℝ N f t) (hk : k ≤ N) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin k f s x = iteratedDerivWithin k f t x := by
  unfold iteratedDerivWithin
  rw [iteratedFDerivWithin_subset hst hs ht (hf.of_le (by exact_mod_cast hk)) hx]

theorem taylor_remainder_successor {f : ℝ → ℝ} {a b α β : ℝ} {m : ℕ}
    (hab : a < b) (hf : TaylorHypotheses f a b (m + 1))
    (hα : α ∈ Icc a b) (hβ : β ∈ Icc a b) (hne : α ≠ β) :
    ∃ x ∈ uIoo α β,
      f β = TaylorPolynomialValue f a b (m + 1) α β +
        iteratedDerivWithin (m + 1) f (Icc a b) x * (β - α) ^ (m + 1) / (m + 1) ! := by
  have hfull : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hsmall : UniqueDiffOn ℝ (uIcc α β) := uniqueDiffOn_uIcc hne
  have hsub : uIcc α β ⊆ Icc a b := uIcc_subset_Icc hα hβ
  have hsubopen : uIoo α β ⊆ Ioo a b := by
    intro x hx
    rcases le_total α β with h | h
    · simp only [uIoo, min_eq_left h, max_eq_right h, mem_Ioo] at hx
      exact ⟨lt_of_le_of_lt hα.1 hx.1, lt_of_lt_of_le hx.2 hβ.2⟩
    · simp only [uIoo, min_eq_right h, max_eq_left h, mem_Ioo] at hx
      exact ⟨lt_of_le_of_lt hβ.1 hx.1, lt_of_lt_of_le hx.2 hα.2⟩
  have hcd : ContDiffOn ℝ m f (Icc a b) := higherExists_contDiffOn
    (by simpa [TaylorHypotheses] using hf.1) (by simpa using hf.2.1)
  have heq : ∀ k ≤ m, EqOn (iteratedDerivWithin k f (uIcc α β))
      (iteratedDerivWithin k f (Icc a b)) (uIcc α β) := by
    intro k hk x hx
    exact iteratedDerivWithin_subset_of_contDiff hsub hsmall hfull hcd hk hx
  have hd : ∀ x ∈ uIoo α β,
      DifferentiableWithinAt ℝ (iteratedDerivWithin m f (Icc a b)) (Icc a b) x := by
    intro x hx
    exact (hf.2.2 x (hsubopen hx)).2
  have hdsmall : DifferentiableOn ℝ (iteratedDerivWithin m f (uIcc α β)) (uIoo α β) := by
    intro x hx
    exact ((hd x hx).mono (Ioo_subset_Icc_self.trans hsub)).congr
      (fun y hy => heq m le_rfl (Ioo_subset_Icc_self hy))
      (heq m le_rfl (Ioo_subset_Icc_self hx))
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange hne (hcd.mono hsub) hdsmall
  have hn : iteratedDerivWithin (m + 1) f (uIcc α β) x =
      iteratedDerivWithin (m + 1) f (Icc a b) x := by
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr (heq m le_rfl) (heq m le_rfl (Ioo_subset_Icc_self hx))]
    simpa only [iteratedDerivWithin_succ] using
      derivWithin_subset hsub (hsmall x (Ioo_subset_Icc_self hx)) (hd x hx)
  have hp : taylorWithinEval f m (uIcc α β) α β =
      TaylorPolynomialValue f a b (m + 1) α β := by
    rw [taylor_within_apply]
    unfold TaylorPolynomialValue
    apply Finset.sum_congr rfl
    intro k hk
    rw [heq k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) left_mem_uIcc]
    simp only [smul_eq_mul]
    ring
  rw [hn, hp] at hrem
  exact ⟨x, hx, by linarith⟩

theorem taylor_remainder {f : ℝ → ℝ} {a b α β : ℝ} {n : ℕ}
    (hab : a < b) (hn : 1 ≤ n) (hf : TaylorHypotheses f a b n)
    (hα : α ∈ Icc a b) (hβ : β ∈ Icc a b) (hne : α ≠ β) :
    ∃ x ∈ uIoo α β,
      f β = TaylorPolynomialValue f a b n α β +
        iteratedDerivWithin n f (Icc a b) x * (β - α) ^ n / n ! := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact taylor_remainder_successor hab hf hα hβ hne

theorem taylor_remainder_bound {f : ℝ → ℝ} {a b α β M : ℝ} {n : ℕ}
    (hab : a < b) (hn : 1 ≤ n) (hf : TaylorHypotheses f a b n)
    (hα : α ∈ Icc a b) (hβ : β ∈ Icc a b) (hne : α ≠ β)
    (hbound : ∀ x ∈ uIoo α β, |iteratedDerivWithin n f (Icc a b) x| ≤ M) :
    |f β - TaylorPolynomialValue f a b n α β| ≤ M * |β - α| ^ n / n ! := by
  obtain ⟨x, hx, hrem⟩ := taylor_remainder hab hn hf hα hβ hne
  have hdiff : f β - TaylorPolynomialValue f a b n α β =
      iteratedDerivWithin n f (Icc a b) x * (β - α) ^ n / n ! := by linarith
  rw [hdiff, abs_div, abs_mul, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ n ! from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound x hx) (pow_nonneg (abs_nonneg _) _))
    (Nat.cast_nonneg _)

theorem taylor_order_one {f : ℝ → ℝ} {a b α β : ℝ}
    (hab : a < b) (hf : TaylorHypotheses f a b 1)
    (hα : α ∈ Icc a b) (hβ : β ∈ Icc a b) (hne : α ≠ β) :
    ∃ x ∈ uIoo α β, f β - f α = (β - α) * derivWithin f (Icc a b) x := by
  obtain ⟨x, hx, hrem⟩ := taylor_remainder hab le_rfl hf hα hβ hne
  refine ⟨x, hx, ?_⟩
  simp only [TaylorPolynomialValue, Finset.sum_range_one, iteratedDerivWithin_zero,
    pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one, iteratedDerivWithin_one,
    pow_one, Nat.factorial_one] at hrem
  linarith

theorem pma5_15 : pma5_15_contract := by
  exact ⟨fun _ _ _ _ _ _ => taylor_remainder,
    fun _ _ _ _ _ _ _ => taylor_remainder_bound,
    fun _ _ _ _ _ => taylor_order_one⟩

/-! ### Boundary and non-vacuity probes -/

theorem higherExists_zero (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) :
    HigherExistsWithin f s 0 x := trivial

/-- The source existence predicate rejects the totalized derivative at the cusp. -/
theorem higherExists_abs_zero_probe :
    ¬ HigherExistsWithin abs (Icc (-1 : ℝ) 1) 1 0 := by
  intro h
  have hd : DifferentiableWithinAt ℝ abs (Icc (-1 : ℝ) 1) 0 := by
    simpa only [iteratedDerivWithin_zero] using h.2
  apply not_differentiableAt_abs_zero
  exact hd.differentiableAt (Icc_mem_nhds (by norm_num) (by norm_num))

/-- Order one recovers the usual MVT hypotheses without asking for endpoint derivatives. -/
theorem taylorHypotheses_one_iff {f : ℝ → ℝ} {a b : ℝ} :
    TaylorHypotheses f a b 1 ↔
      ContinuousOn f (Icc a b) ∧ DifferentiableOn ℝ f (Ioo a b) := by
  constructor
  · intro h
    refine ⟨by simpa only [Nat.sub_self, iteratedDerivWithin_zero] using h.2.1, ?_⟩
    intro x hx
    have hd : DifferentiableWithinAt ℝ f (Icc a b) x := by
      simpa only [iteratedDerivWithin_zero] using (h.2.2 x hx).2
    exact hd.mono Ioo_subset_Icc_self
  · intro h
    refine ⟨fun _ _ => trivial, ?_, ?_⟩
    · simpa only [Nat.sub_self, iteratedDerivWithin_zero] using h.1
    · intro x hx
      refine ⟨Eventually.of_forall (fun _ => trivial), ?_⟩
      simpa only [iteratedDerivWithin_zero] using
        ((h.2 x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).differentiableWithinAt


end Rudin.PMA.Chapter05


/- Assembly source: Chapter05VectorDraft.lean -/

noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace

namespace Rudin.PMA.Chapter05

/-! ### PMA-5.16: Real-parameter complex and Euclidean derivatives -/

def VectorDerivativeWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (a b x : ℝ) : Prop :=
  a < b ∧ x ∈ Icc a b ∧
    Tendsto (fun t => ‖(t - x)⁻¹ • (f t - f x) - v‖)
      (𝓝[Icc a b \ {x}] x) (𝓝 0)

theorem vectorDerivativeWithin_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (a b x : ℝ) :
    VectorDerivativeWithin f v a b x ↔
      a < b ∧ x ∈ Icc a b ∧ HasDerivWithinAt f v (Icc a b) x := by
  unfold VectorDerivativeWithin
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact tendsto_iff_norm_sub_tendsto_zero.symm

theorem complex_derivative_components (f : ℝ → ℂ) (v : ℂ) (s : Set ℝ) (x : ℝ) :
    HasDerivWithinAt f v s x ↔
      HasDerivWithinAt (fun t => (f t).re) v.re s x ∧
      HasDerivWithinAt (fun t => (f t).im) v.im s x := by
  constructor
  · intro h
    exact ⟨Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt x h,
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt x h⟩
  · rintro ⟨hr, hi⟩
    convert hr.ofReal_comp.add (hi.ofReal_comp.mul_const Complex.I) using 1
    · funext t
      exact (Complex.re_add_im (f t)).symm
    · exact (Complex.re_add_im v).symm

theorem euclidean_derivative_components (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (s : Set ℝ) (x : ℝ) :
    HasDerivWithinAt f v s x ↔
      ∀ i, HasDerivWithinAt (fun t => f t i) (v i) s x := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  constructor
  · intro h
    exact hasDerivWithinAt_pi.mp (e.hasFDerivAt.comp_hasDerivWithinAt x h)
  · intro h
    have hh := hasDerivWithinAt_pi.mpr h
    exact e.symm.hasFDerivAt.comp_hasDerivWithinAt x hh

def pma5_16_contract : Prop :=
  (∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (a b x : ℝ),
    VectorDerivativeWithin f v a b x ↔
      a < b ∧ x ∈ Icc a b ∧ HasDerivWithinAt f v (Icc a b) x) ∧
  (∀ (f : ℝ → ℂ) (v : ℂ) (s : Set ℝ) (x : ℝ),
    HasDerivWithinAt f v s x ↔
      HasDerivWithinAt (fun t => (f t).re) v.re s x ∧
      HasDerivWithinAt (fun t => (f t).im) v.im s x) ∧
  (∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (s : Set ℝ) (x : ℝ),
    HasDerivWithinAt f v s x ↔
      ∀ i, HasDerivWithinAt (fun t => f t i) (v i) s x) ∧
  (∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (v w : E) (s : Set ℝ) (x : ℝ),
    HasDerivWithinAt f v s x → HasDerivWithinAt g w s x →
      ContinuousWithinAt f s x ∧ HasDerivWithinAt (fun t => f t + g t) (v + w) s x) ∧
  (∀ (f g : ℝ → ℂ) (v w : ℂ) (s : Set ℝ) (x : ℝ),
    HasDerivWithinAt f v s x → HasDerivWithinAt g w s x →
      HasDerivWithinAt (fun t => f t * g t) (v * g x + f x * w) s x ∧
      (g x ≠ 0 → HasDerivWithinAt (fun t => f t / g t)
        ((v * g x - f x * w) / (g x)^2) (s ∩ {t | g t ≠ 0}) x)) ∧
  (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : ℝ → E) (v w : E) (s : Set ℝ) (x : ℝ),
    HasDerivWithinAt f v s x → HasDerivWithinAt g w s x →
      HasDerivWithinAt (fun t => ⟪f t, g t⟫_ℝ) (⟪v, g x⟫_ℝ + ⟪f x, w⟫_ℝ) s x)

theorem pma5_16 : pma5_16_contract := by
  refine ⟨vectorDerivativeWithin_iff, complex_derivative_components,
    euclidean_derivative_components, ?_, ?_, ?_⟩
  · intro E _ _ f g v w s x hf hg
    exact ⟨hf.continuousWithinAt, hf.add hg⟩
  · intro f g v w s x hf hg
    exact ⟨hf.mul hg, fun h => (hf.div hg h).mono inter_subset_left⟩
  · intro E _ _ f g v w s x hf hg
    simpa only [add_comm] using hf.inner ℝ hg

/-! ### PMA-5.17: The scalar mean-value equality fails for a circle -/

def circleCurve (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)
def circleVelocity (x : ℝ) : ℂ := Complex.I * circleCurve x

def pma5_17_contract : Prop :=
  (∀ x, circleCurve x = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I) ∧
  circleCurve 0 = 1 ∧ circleCurve (2 * Real.pi) = 1 ∧
  (∀ x, HasDerivAt circleCurve (circleVelocity x) x ∧ ‖circleVelocity x‖ = 1) ∧
  ¬ ∃ x ∈ Ioo 0 (2 * Real.pi),
    circleCurve (2 * Real.pi) - circleCurve 0 = (2 * Real.pi) • circleVelocity x

theorem circle_derivative (x : ℝ) : HasDerivAt circleCurve (circleVelocity x) x := by
  change HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
    (Complex.I * Complex.exp ((x : ℂ) * Complex.I)) x
  simpa [mul_comm] using ((hasDerivAt_id x).ofReal_comp.mul_const Complex.I).cexp

theorem circle_velocity_norm (x : ℝ) : ‖circleVelocity x‖ = 1 := by
  simp [circleVelocity, circleCurve, Complex.norm_exp]

theorem pma5_17 : pma5_17_contract := by
  have h0 : circleCurve 0 = 1 := by simp [circleCurve]
  have hp : circleCurve (2 * Real.pi) = 1 := by
    simp [circleCurve, Complex.ofReal_mul, Complex.exp_two_pi_mul_I]
  refine ⟨?_, h0, hp, fun x => ⟨circle_derivative x, circle_velocity_norm x⟩, ?_⟩
  · intro x
    simpa [circleCurve] using Complex.exp_mul_I (x : ℂ)
  · rintro ⟨x, hx, h⟩
    have hn := congrArg norm h
    rw [hp, h0, sub_self, norm_zero, norm_smul, circle_velocity_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at hn
    exact (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne' hn.symm

/-! ### PMA-5.18: The complex l'Hôpital counterexample -/

def complexHopitalPhase (x : ℝ) : ℂ := Complex.exp (Complex.I / (x : ℂ)^2)
def complexHopitalG (x : ℝ) : ℂ := (x : ℂ) + (x : ℂ)^2 * complexHopitalPhase x
def complexHopitalVelocity (x : ℝ) : ℂ :=
  1 + (2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)) * complexHopitalPhase x

def pma5_18_contract : Prop :=
  (∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x ∧
    HasDerivAt complexHopitalG (complexHopitalVelocity x) x ∧
    complexHopitalG x ≠ 0 ∧ complexHopitalVelocity x ≠ 0 ∧
    ‖2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)‖ - 1 ≤ ‖complexHopitalVelocity x‖ ∧
    2 / x - 1 ≤ ‖2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)‖ - 1 ∧
    ‖(1 : ℂ) / complexHopitalVelocity x‖ ≤ x / (2 - x)) ∧
  Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 0) ∧
  Tendsto complexHopitalG (𝓝[>] 0) (𝓝 0) ∧
  Tendsto (fun x : ℝ => (x : ℂ) / complexHopitalG x) (𝓝[>] 0) (𝓝 1) ∧
  Tendsto (fun x => (1 : ℂ) / complexHopitalVelocity x) (𝓝[>] 0) (𝓝 0)

theorem complexHopitalPhase_norm (x : ℝ) : ‖complexHopitalPhase x‖ = 1 := by
  simp [complexHopitalPhase, Complex.norm_exp, Complex.div_re, ← Complex.ofReal_pow]

theorem complexHopital_derivative (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt complexHopitalG (complexHopitalVelocity x) x := by
  have hc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hid := hasDerivAt_id (x : ℂ)
  have hs := hid.pow 2
  have he := ((hasDerivAt_const (x : ℂ) Complex.I).div hs (pow_ne_zero 2 hc)).cexp
  have h := (hid.add (hs.mul he)).comp_ofReal
  convert h using 1
  · rfl
  · simp only [complexHopitalVelocity, complexHopitalPhase, mul_one,
      Nat.cast_ofNat, zero_mul, zero_sub, Pi.pow_apply, Pi.div_apply, id_eq]
    norm_num
    field_simp [hc]
    ring

theorem complexHopital_coefficient_lower (x : ℝ) (hx : 0 < x) :
    2 / x ≤ ‖2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)‖ := by
  have h := Complex.abs_im_le_norm (2 * (x : ℂ) - 2 * Complex.I / (x : ℂ))
  have he : 2 * x / (x * x) = 2 / x := by field_simp
  simpa [Complex.div_im, Complex.normSq_apply, abs_of_pos hx, abs_of_nonneg (le_of_lt hx),
    div_pow, mul_div_cancel_left₀, hx.ne', div_self, abs_div, he] using h

theorem complexHopital_velocity_lower (x : ℝ) :
    ‖2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)‖ - 1 ≤ ‖complexHopitalVelocity x‖ := by
  have h := norm_sub_le (complexHopitalVelocity x) (1 : ℂ)
  have he : complexHopitalVelocity x - 1 =
      (2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)) * complexHopitalPhase x := by
    simp [complexHopitalVelocity]
  rw [he, norm_mul, complexHopitalPhase_norm, mul_one, norm_one] at h
  linarith

theorem complexHopital_nonzero (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    complexHopitalG x ≠ 0 ∧ complexHopitalVelocity x ≠ 0 := by
  constructor
  · intro hzero
    have h := norm_sub_le (complexHopitalG x) ((x : ℂ)^2 * complexHopitalPhase x)
    have he : complexHopitalG x - (x : ℂ)^2 * complexHopitalPhase x = (x : ℂ) := by
      simp [complexHopitalG]
    rw [he, hzero, norm_zero, zero_add, norm_mul, norm_pow,
      complexHopitalPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx.1] at h
    nlinarith [mul_pos hx.1 (sub_pos.mpr hx.2)]
  · have h := complexHopital_velocity_lower x
    have hc := complexHopital_coefficient_lower x hx.1
    have hdiv : 2 < 2 / x := (lt_div_iff₀ hx.1).mpr (by linarith [hx.2])
    exact norm_pos_iff.mp (by linarith)

theorem complexHopital_ratio_bound (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖(1 : ℂ) / complexHopitalVelocity x‖ ≤ x / (2 - x) := by
  have h := complexHopital_velocity_lower x
  have hc := complexHopital_coefficient_lower x hx.1
  have hl : 0 < 2 / x - 1 := by
    have : 2 < 2 / x := (lt_div_iff₀ hx.1).mpr (by linarith [hx.2])
    linarith
  rw [norm_div, norm_one]
  calc
    1 / ‖complexHopitalVelocity x‖ ≤ 1 / (2 / x - 1) :=
      one_div_le_one_div_of_le hl (by linarith)
    _ = x / (2 - x) := by
      field_simp [hx.1.ne', (show 2 - x ≠ 0 by linarith [hx.2])]

theorem complexHopital_small_term :
    Tendsto (fun x : ℝ => (x : ℂ) * complexHopitalPhase x) (𝓝 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_mul, complexHopitalPhase_norm, mul_one, Complex.ofReal_zero, norm_zero]
    using (Complex.continuous_ofReal.tendsto (0 : ℝ)).norm

theorem complexHopitalG_limit : Tendsto complexHopitalG (𝓝 0) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hs := hi.mul complexHopital_small_term
  have h := hi.add hs
  change Tendsto (fun x : ℝ => (x : ℂ) + (x : ℂ)^2 * complexHopitalPhase x) (𝓝 0) (𝓝 0)
  simpa only [zero_mul, zero_add, Pi.add_apply, Pi.mul_apply, pow_two, mul_assoc] using h

theorem complexHopital_quotient_limit :
    Tendsto (fun x : ℝ => (x : ℂ) / complexHopitalG x) (𝓝[>] 0) (𝓝 1) := by
  have hd : Tendsto (fun x : ℝ => (1 : ℂ) + (x : ℂ) * complexHopitalPhase x)
      (𝓝[>] 0) (𝓝 1) := by
    simpa only [Pi.add_apply, add_zero] using
      (tendsto_const_nhds (x := (1 : ℂ))).add
        (complexHopital_small_term.mono_left nhdsWithin_le_nhds)
  have hi : Tendsto (fun x : ℝ => (1 : ℂ) / (1 + (x : ℂ) * complexHopitalPhase x))
      (𝓝[>] 0) (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1 : ℂ))).div hd
      (one_ne_zero : (1 : ℂ) ≠ 0) using 1
    simp
  apply hi.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have he : complexHopitalG x = (x : ℂ) * (1 + (x : ℂ) * complexHopitalPhase x) := by
    unfold complexHopitalG
    ring
  rw [he, div_mul_eq_div_div, div_self hc]

theorem complexHopital_derivative_quotient_limit :
    Tendsto (fun x => (1 : ℂ) / complexHopitalVelocity x) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _))
    (show ∀ᶠ x in 𝓝[>] (0 : ℝ),
      ‖(1 : ℂ) / complexHopitalVelocity x‖ ≤ x / (2 - x) from ?_) ?_
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact complexHopital_ratio_bound x hx
  · have ht : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    convert ht.div (tendsto_const_nhds.sub ht)
      (by norm_num : (2 : ℝ) - 0 ≠ 0) using 1
    simp

theorem pma5_18 : pma5_18_contract := by
  refine ⟨?_, ?_, complexHopitalG_limit.mono_left nhdsWithin_le_nhds,
    complexHopital_quotient_limit, complexHopital_derivative_quotient_limit⟩
  · intro x hx
    exact ⟨(hasDerivAt_id x).ofReal_comp, complexHopital_derivative x hx.1.ne',
      (complexHopital_nonzero x hx).1, (complexHopital_nonzero x hx).2,
      complexHopital_velocity_lower x, sub_le_sub_right (complexHopital_coefficient_lower x hx.1) 1,
      complexHopital_ratio_bound x hx⟩
  · simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

/-! ### PMA-5.19: The norm mean-value inequality and its consequences -/

def pma5_19_contract : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f f' : ℝ → E) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) →
    (∃ x ∈ Ioo a b, ‖f b - f a‖ ≤ (b - a) * ‖f' x‖) ∧
    (∀ M : ℝ, (∀ x ∈ Ioo a b, ‖f' x‖ ≤ M) → ‖f b - f a‖ ≤ (b - a) * M) ∧
    (BddAbove ((fun x => ‖f' x‖) '' Ioo a b) →
      ‖f b - f a‖ ≤ (b - a) * sSup ((fun x => ‖f' x‖) '' Ioo a b))

theorem exists_norm_mean_value {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f f' : ℝ → E) (a b : ℝ) (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ x ∈ Ioo a b, ‖f b - f a‖ ≤ (b - a) * ‖f' x‖ := by
  let v := f b - f a
  have hg : ContinuousOn (fun t => ⟪v, f t⟫_ℝ) (Icc a b) := continuousOn_const.inner hf
  have hgd : ∀ x ∈ Ioo a b,
      HasDerivAt (fun t => ⟪v, f t⟫_ℝ) ⟪v, f' x⟫_ℝ x := by
    intro x hx
    simpa using (hasDerivAt_const x v).inner ℝ (hd x hx)
  obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope
    (fun t => ⟪v, f t⟫_ℝ) (fun t => ⟪v, f' t⟫_ℝ) hab hg hgd
  refine ⟨x, hx, ?_⟩
  rw [← inner_sub_right, show f b - f a = v from rfl, real_inner_self_eq_norm_sq] at heq
  have he : ‖v‖^2 = (b - a) * ⟪v, f' x⟫_ℝ := by
    have := (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp heq
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (real_inner_le_norm v (f' x)) (sub_nonneg.mpr hab.le)
  change ‖v‖ ≤ (b - a) * ‖f' x‖
  by_cases hv : ‖v‖ = 0
  · rw [hv]
    positivity
  · have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    nlinarith

theorem pma5_19 : pma5_19_contract := by
  intro E _ _ f f' a b hab hf hd
  have hm := exists_norm_mean_value f f' a b hab hf hd
  have hu : ∀ M : ℝ, (∀ x ∈ Ioo a b, ‖f' x‖ ≤ M) →
      ‖f b - f a‖ ≤ (b - a) * M := by
    intro M hM
    obtain ⟨x, hx, h⟩ := hm
    exact h.trans (mul_le_mul_of_nonneg_left (hM x hx) (sub_nonneg.mpr hab.le))
  refine ⟨hm, hu, ?_⟩
  intro hbdd
  exact hu _ (fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩)

/-! Boundary and nonvacuity probes for the source-sensitive cases. -/

theorem vector_derivative_left_endpoint_probe :
    VectorDerivativeWithin (fun t : ℝ => (t : ℂ)) 1 0 1 0 := by
  apply (vectorDerivativeWithin_iff _ _ _ _ _).mpr
  exact ⟨by norm_num, by simp, (hasDerivAt_id (0 : ℝ)).ofReal_comp.hasDerivWithinAt⟩

theorem vector_derivative_right_endpoint_probe :
    VectorDerivativeWithin (fun t : ℝ => (t : ℂ)) 1 0 1 1 := by
  apply (vectorDerivativeWithin_iff _ _ _ _ _).mpr
  exact ⟨by norm_num, by simp, (hasDerivAt_id (1 : ℝ)).ofReal_comp.hasDerivWithinAt⟩

theorem vector_derivative_degenerate_interval_probe {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (v : E) (a : ℝ) :
    ¬ VectorDerivativeWithin f v a a a := by
  intro h
  exact (lt_irrefl a) h.1

theorem complexHopital_distinct_limits_probe :
    ¬ Tendsto (fun x : ℝ => (x : ℂ) / complexHopitalG x) (𝓝[>] 0) (𝓝 0) := by
  intro h
  exact one_ne_zero (tendsto_nhds_unique complexHopital_quotient_limit h)


end Rudin.PMA.Chapter05


/- Assembly source: Chapter05Integration.lean -/

noncomputable section
open Set Filter
open scoped Topology

namespace Rudin.PMA.Chapter05

/-- The vector norm-limit uses exactly the source's interior approach, including
one-sided derivatives at the endpoints of the nondegenerate closed interval. -/
theorem vectorDerivativeWithin_source_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    VectorDerivativeWithin f v a b x ↔
      Tendsto (fun t => ‖(t - x)⁻¹ • (f t - f x) - v‖)
        (𝓝[Ioo a b \ {x}] x) (𝓝 0) := by
  rw [interval_punctured_Ioo_eq_Icc hab hx]
  simp only [VectorDerivativeWithin, hab, hx, true_and]

end Rudin.PMA.Chapter05
