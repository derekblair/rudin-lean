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
