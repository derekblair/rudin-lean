import Rudin.PMA.Chapter09.Rank

/-!
The geometric consequences attached to PMA 9.32 are stated as exact image,
projection, and level-set identities. The graph map takes values in the ambient
space, with its residual component in the null space of the projection, as in
`pma9_32`. No extra smoothness or rank hypothesis is imposed on these consequences.
-/

noncomputable section
open Set
namespace Rudin.PMA.Chapter09

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The projection, with its codomain restricted to the range of A. -/
def rankRangeProjection (A : E →L[ℝ] F) (P : F →L[ℝ] F)
    (hPrange : P.toLinearMap.range = A.toLinearMap.range) :
    F →L[ℝ] A.toLinearMap.range :=
  P.codRestrict A.toLinearMap.range
    (fun y => hPrange ▸ LinearMap.mem_range_self P.toLinearMap y)

theorem rankProjection_fixes_range (A : E →L[ℝ] F) (P : F →L[ℝ] F)
    (hP : ∀ y, P (P y) = P y)
    (hPrange : P.toLinearMap.range = A.toLinearMap.range)
    (y : A.toLinearMap.range) : P y = y := by
  have hy : (y : F) ∈ P.toLinearMap.range := hPrange.symm ▸ y.property
  obtain ⟨z, hz⟩ := hy
  change P z = (y : F) at hz
  rw [← hz, hP]

/-- PMA 9.32: the local image is precisely the graph over A(V). -/
theorem pma9_32_graph_image (f : E → F) (A : E →L[ℝ] F)
    (H : OpenPartialHomeomorph E E) (φ : A.toLinearMap.range → F)
    (hgraph : ∀ x ∈ H.source, f (H x) = A x + φ (A.rangeRestrict x)) :
    f '' H.target =
      (fun y : A.toLinearMap.range => (y : F) + φ y) '' (A.rangeRestrict '' H.source) := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨A.rangeRestrict (H.symm u), ⟨H.symm u, H.map_target hu, rfl⟩, ?_⟩
    change A (H.symm u) + φ (A.rangeRestrict (H.symm u)) = f u
    rw [← hgraph _ (H.map_target hu), H.right_inv hu]
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨H x, H.map_source hx, hgraph x hx⟩

/-- PMA 9.32, equation (81): projection is a bijection from the local image
onto the open subset A(V) of the range. -/
theorem pma9_32_projection_bijOn (f : E → F) (A : E →L[ℝ] F)
    (P : F →L[ℝ] F) (hP : ∀ y, P (P y) = P y)
    (hPrange : P.toLinearMap.range = A.toLinearMap.range)
    (H : OpenPartialHomeomorph E E) (φ : A.toLinearMap.range → F)
    (hφ : ∀ y, P (φ y) = 0)
    (hgraph : ∀ x ∈ H.source, f (H x) = A x + φ (A.rangeRestrict x)) :
    Set.BijOn (rankRangeProjection A P hPrange) (f '' H.target)
      (A.rangeRestrict '' H.source) := by
  have himage := pma9_32_graph_image f A H φ hgraph
  have hproj (y : A.toLinearMap.range) :
      rankRangeProjection A P hPrange ((y : F) + φ y) = y := by
    apply Subtype.ext
    change P ((y : F) + φ y) = y
    rw [map_add, rankProjection_fixes_range A P hP hPrange, hφ, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [himage] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rwa [hproj]
  · intro y hy z hz heq
    rw [himage] at hy hz
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨v, hv, rfl⟩ := hz
    rw [hproj, hproj] at heq
    rw [heq]
  · intro y hy
    refine ⟨(y : F) + φ y, ?_, hproj y⟩
    rw [himage]
    exact ⟨y, hy, rfl⟩

/-- PMA 9.32, equation (81): a point of the local image is reconstructed
from its projection and the graph function. -/
theorem pma9_32_graph_reconstruct (f : E → F) (A : E →L[ℝ] F)
    (P : F →L[ℝ] F) (hP : ∀ y, P (P y) = P y)
    (hPrange : P.toLinearMap.range = A.toLinearMap.range)
    (H : OpenPartialHomeomorph E E) (φ : A.toLinearMap.range → F)
    (hφ : ∀ y, P (φ y) = 0)
    (hgraph : ∀ x ∈ H.source, f (H x) = A x + φ (A.rangeRestrict x))
    {y : F} (hy : y ∈ f '' H.target) :
    y = P y + φ (rankRangeProjection A P hPrange y) := by
  rw [pma9_32_graph_image f A H φ hgraph] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hproj : rankRangeProjection A P hPrange ((z : F) + φ z) = z := by
    apply Subtype.ext
    change P ((z : F) + φ z) = z
    rw [map_add, rankProjection_fixes_range A P hP hPrange, hφ, add_zero]
  rw [hproj, map_add, rankProjection_fixes_range A P hP hPrange, hφ, add_zero]

/-- PMA 9.32: in the transformed coordinates the level sets are exactly
those of A. -/
theorem pma9_32_level_eq_iff (f : E → F) (A : E →L[ℝ] F)
    (P : F →L[ℝ] F) (hP : ∀ y, P (P y) = P y)
    (hPrange : P.toLinearMap.range = A.toLinearMap.range)
    (H : OpenPartialHomeomorph E E) (φ : A.toLinearMap.range → F)
    (hφ : ∀ y, P (φ y) = 0)
    (hgraph : ∀ x ∈ H.source, f (H x) = A x + φ (A.rangeRestrict x))
    {x y : E} (hx : x ∈ H.source) (hy : y ∈ H.source) :
    f (H x) = f (H y) ↔ A x = A y := by
  constructor
  · intro h
    have hp := congrArg P h
    rw [hgraph x hx, hgraph y hy, map_add, map_add, hφ, hφ,
      add_zero, add_zero] at hp
    have hPx : P (A x) = A x := rankProjection_fixes_range A P hP hPrange (A.rangeRestrict x)
    have hPy : P (A y) = A y := rankProjection_fixes_range A P hP hPrange (A.rangeRestrict y)
    rwa [hPx, hPy] at hp
  · intro h
    have h' : A.rangeRestrict x = A.rangeRestrict y := Subtype.ext h
    rw [hgraph x hx, hgraph y hy, h, h']

/-- PMA 9.32: H carries the intersection of V with a translate of ker(A)
onto the corresponding local level set of f. -/
theorem pma9_32_level_image (f : E → F) (A : E →L[ℝ] F)
    (P : F →L[ℝ] F) (hP : ∀ y, P (P y) = P y)
    (hPrange : P.toLinearMap.range = A.toLinearMap.range)
    (H : OpenPartialHomeomorph E E) (φ : A.toLinearMap.range → F)
    (hφ : ∀ y, P (φ y) = 0)
    (hgraph : ∀ x ∈ H.source, f (H x) = A x + φ (A.rangeRestrict x))
    {x₀ : E} (hx₀ : x₀ ∈ H.source) :
    H '' {x | x ∈ H.source ∧ x - x₀ ∈ A.toLinearMap.ker} =
      {u | u ∈ H.target ∧ f u = f (H x₀)} := by
  ext u
  constructor
  · rintro ⟨x, ⟨hx, hk⟩, rfl⟩
    refine ⟨H.map_source hx, ?_⟩
    apply (pma9_32_level_eq_iff f A P hP hPrange H φ hφ hgraph hx hx₀).mpr
    change A (x - x₀) = 0 at hk
    exact sub_eq_zero.mp (by simpa only [map_sub] using hk)
  · rintro ⟨hu, hf⟩
    refine ⟨H.symm u, ⟨H.map_target hu, ?_⟩, H.right_inv hu⟩
    have heq := (pma9_32_level_eq_iff f A P hP hPrange H φ hφ hgraph
      (H.map_target hu) hx₀).mp (by simpa only [H.right_inv hu] using hf)
    change A (H.symm u - x₀) = 0
    rw [map_sub, heq, sub_self]

/-- The dimension assertion accompanying PMA 9.32 is rank-nullity. -/
theorem pma9_32_kernel_dimension [FiniteDimensional ℝ E] (A : E →L[ℝ] F) :
    Module.finrank ℝ A.toLinearMap.ker =
      Module.finrank ℝ E - Module.finrank ℝ A.toLinearMap.range := by
  have h := A.toLinearMap.finrank_range_add_finrank_ker
  omega

end Rudin.PMA.Chapter09
