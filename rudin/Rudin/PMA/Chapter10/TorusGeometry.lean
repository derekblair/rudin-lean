import Rudin.PMA.Chapter10.Torus

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma torus_revolution_radius_pos {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc 0 a) (θ : ℝ) :
    0 < b + t * Real.sin θ := by
  have h := mul_nonneg ht.1 (show 0 ≤ Real.sin θ + 1 by linarith [Real.neg_one_le_sin θ])
  nlinarith [ht.2]

lemma torusMap_yz_sq (b : ℝ) (u : Coord 3) :
    (torusMap b u) 1 ^ 2 + (torusMap b u) 2 ^ 2 = (b + u 0 * Real.sin (u 1)) ^ 2 := by
  simp only [torusMap, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero]
  calc
    _ = (b + u 0 * Real.sin (u 1)) ^ 2 * (Real.cos (u 2) ^ 2 + Real.sin (u 2) ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

lemma torusMap_yz_radius (b : ℝ) (u : Coord 3) (hρ : 0 ≤ b + u 0 * Real.sin (u 1)) :
    Real.sqrt ((torusMap b u) 1 ^ 2 + (torusMap b u) 2 ^ 2) = b + u 0 * Real.sin (u 1) := by
  rw [torusMap_yz_sq, Real.sqrt_sq hρ]

def torusLevel (b : ℝ) (x : Euclidean 3) : ℝ :=
  x 0 ^ 2 + (Real.sqrt (x 1 ^ 2 + x 2 ^ 2) - b) ^ 2

lemma torusLevel_map (b : ℝ) (u : Coord 3) (hρ : 0 ≤ b + u 0 * Real.sin (u 1)) :
    torusLevel b (torusMap b u) = u 0 ^ 2 := by
  rw [torusLevel, torusMap_yz_radius b u hρ]
  simp only [torusMap, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_zero, add_sub_cancel_left]
  calc
    _ = u 0 ^ 2 * (Real.cos (u 1) ^ 2 + Real.sin (u 1) ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

lemma torusMap_image {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    torusMap b '' (torusCell a ha).carrier = solidTorus a b := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have ht : u 0 ∈ Icc 0 a := (Cell.mem_carrier.mp hu) 0
    change torusLevel b (torusMap b u) ≤ a ^ 2
    rw [torusLevel_map b u (torus_revolution_radius_pos hab ht (u 1)).le]
    exact pow_le_pow_left₀ ht.1 ht.2 2
  · intro hx
    obtain ⟨ρ, φ, hρ, hφ, hφc, hφs, hρsq⟩ := exists_nonnegative_polar (x 1) (x 2)
    have hsqrt : Real.sqrt (x 1 ^ 2 + x 2 ^ 2) = ρ := by rw [← hρsq, Real.sqrt_sq hρ]
    obtain ⟨t, θ, ht, hθ, hθc, hθs, htsq⟩ := exists_nonnegative_polar (x 0) (ρ - b)
    have hta : t ≤ a := by
      apply (sq_le_sq₀ ht ha.le).mp
      change x 0 ^ 2 + (Real.sqrt (x 1 ^ 2 + x 2 ^ 2) - b) ^ 2 ≤ a ^ 2 at hx
      rw [htsq, ← hsqrt]
      exact hx
    have hr : b + t * Real.sin θ = ρ := by linarith
    refine ⟨![t, θ, φ], ?_, ?_⟩
    · rw [Cell.mem_carrier]
      intro i
      fin_cases i
      · exact ⟨ht, hta⟩
      · exact hθ
      · exact hφ
    · ext i
      fin_cases i
      · simpa [torusMap] using hθc
      · simpa [torusMap, hr] using hφc
      · simpa [torusMap, hr] using hφs

lemma torusCell_mem_interior {a : ℝ} (ha : 0 < a) {u : Coord 3} :
    u ∈ interior (torusCell a ha).carrier ↔
      u 0 ∈ Ioo 0 a ∧ u 1 ∈ Ioo 0 (2 * Real.pi) ∧ u 2 ∈ Ioo 0 (2 * Real.pi) := by
  rw [Cell.carrier, ← pi_univ_Icc, interior_pi_set finite_univ]
  simp [torusCell, Set.mem_pi, Fin.forall_fin_succ]

lemma angle_eq_of_sin_cos {θ φ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi))
    (hφ : φ ∈ Ioo 0 (2 * Real.pi)) (hc : Real.cos θ = Real.cos φ)
    (hs : Real.sin θ = Real.sin φ) : θ = φ := by
  have hp : (1, θ - Real.pi) ∈ polarCoord.target :=
    ⟨by norm_num, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
  have hq : (1, φ - Real.pi) ∈ polarCoord.target :=
    ⟨by norm_num, ⟨by linarith [hφ.1], by linarith [hφ.2]⟩⟩
  have he := polarCoord.symm.injOn hp hq (by
    ext <;> simp [polarCoord, Real.cos_sub, Real.sin_sub, hc, hs])
  have := congrArg Prod.snd he
  dsimp at this
  linarith

lemma torusMap_injOn {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    InjOn (torusMap b) (interior (torusCell a ha).carrier) := by
  intro u hu v hv huv
  rcases (torusCell_mem_interior ha).mp hu with ⟨hu0, hu1, hu2⟩
  rcases (torusCell_mem_interior ha).mp hv with ⟨hv0, hv1, hv2⟩
  have hρu := torus_revolution_radius_pos hab ⟨hu0.1.le, hu0.2.le⟩ (u 1)
  have hρv := torus_revolution_radius_pos hab ⟨hv0.1.le, hv0.2.le⟩ (v 1)
  have ht : u 0 = v 0 := by
    apply (sq_eq_sq₀ hu0.1.le hv0.1.le).mp
    have he := congrArg (torusLevel b) huv
    simpa only [torusLevel_map b u hρu.le, torusLevel_map b v hρv.le] using he
  have hρ : b + u 0 * Real.sin (u 1) = b + v 0 * Real.sin (v 1) := by
    have he := congrArg (fun x : Euclidean 3 => Real.sqrt (x 1 ^ 2 + x 2 ^ 2)) huv
    simpa only [torusMap_yz_radius b u hρu.le, torusMap_yz_radius b v hρv.le] using he
  have h0 := congrArg (fun x : Euclidean 3 => x 0) huv
  have h1 := congrArg (fun x : Euclidean 3 => x 1) huv
  have h2 := congrArg (fun x : Euclidean 3 => x 2) huv
  simp only [torusMap, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  have hθ : u 1 = v 1 := by
    apply angle_eq_of_sin_cos hu1 hv1
    · rw [← ht] at h0
      exact mul_left_cancel₀ hu0.1.ne' h0
    · rw [← ht] at hρ
      exact mul_left_cancel₀ hu0.1.ne' (add_left_cancel hρ)
  have hφ : u 2 = v 2 := by
    apply angle_eq_of_sin_cos hu2 hv2
    · rw [← hρ] at h1
      exact mul_left_cancel₀ hρu.ne' h1
    · rw [← hρ] at h2
      exact mul_left_cancel₀ hρu.ne' h2
  ext i
  fin_cases i
  · exact ht
  · exact hθ
  · exact hφ

lemma torusUnitNormal_norm (u : Coord 2) : ‖torusUnitNormal u‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [torusUnitNormal, coordEquivEuclidean_apply_coordinate,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_pow]
  calc
    _ = Real.cos (u 0) ^ 2 + Real.sin (u 0) ^ 2 *
      (Real.cos (u 1) ^ 2 + Real.sin (u 1) ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one, Real.cos_sq_add_sin_sq]

lemma torusOuterMap_add_normal (a b s : ℝ) (u : Coord 2) :
    torusOuterMap a b u + s • torusUnitNormal u = torusMap b ![a + s, u 0, u 1] := by
  ext i
  fin_cases i <;> simp [torusOuterMap, torusMap, torusUnitNormal, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul] <;> ring

lemma torusOuterMap_outward {a b : ℝ} (ha : 0 < a) (hab : a < b) (u : Coord 2)
    {s : ℝ} (hs : s ∈ Ioo 0 (b - a)) :
    torusOuterMap a b u + s • torusUnitNormal u ∉ solidTorus a b := by
  rw [torusOuterMap_add_normal]
  have has : 0 < a + s := add_pos ha hs.1
  have hbs : a + s < b := by linarith [hs.2]
  have hρ := torus_revolution_radius_pos hbs (show a + s ∈ Icc 0 (a + s) from ⟨has.le, le_rfl⟩) (u 0)
  change ¬ torusLevel b (torusMap b ![a + s, u 0, u 1]) ≤ a ^ 2
  rw [torusLevel_map b _ hρ.le]
  simp only [Matrix.cons_val_zero]
  nlinarith [mul_pos ha hs.1, sq_pos_of_pos hs.1]

lemma solidTorus_z_le {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : Euclidean 3} (hx : x ∈ solidTorus a b) : x 2 ≤ b + a := by
  rw [← torusMap_image ha hab] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have ht : u 0 ∈ Icc 0 a := (Cell.mem_carrier.mp hu) 0
  have hρ := torus_revolution_radius_pos hab ht (u 1)
  have h1 := mul_le_mul_of_nonneg_left (Real.sin_le_one (u 1)) ht.1
  have h2 := mul_le_mul_of_nonneg_left (Real.sin_le_one (u 2)) hρ.le
  change (b + u 0 * Real.sin (u 1)) * Real.sin (u 2) ≤ b + a
  nlinarith [ht.2]

lemma torusOuterMap_top (a b : ℝ) :
    torusOuterMap a b ![Real.pi / 2, Real.pi / 2] = (b + a) • coordinateVector 3 2 := by
  ext i
  fin_cases i <;>
    simp [torusOuterMap, torusMap, coordinateVector, EuclideanSpace.basisFun_apply,
      PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]

end Rudin.PMA.Chapter10
