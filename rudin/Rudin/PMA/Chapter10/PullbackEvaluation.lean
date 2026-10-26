import Rudin.PMA.Chapter10.SurfaceMaps

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma evaluateForm_pullback {n m k : ℕ} (A : Operator n m)
    (v : Fin k → Euclidean n) (a : CotangentExterior m) :
    evaluateForm k v (ExteriorAlgebra.map (covectorPullback A) a) =
      evaluateForm k (fun j => A (v j)) a := by
  have he : (evaluateForm k v).comp (ExteriorAlgebra.map (covectorPullback A)).toLinearMap =
      evaluateForm k (fun j => A (v j)) := by
    apply ExteriorAlgebra.lhom_ext
    intro d
    apply AlternatingMap.ext
    intro w
    change evaluateForm k v (ExteriorAlgebra.map (covectorPullback A)
      (ExteriorAlgebra.ιMulti ℝ d w)) =
      evaluateForm k (fun j => A (v j)) (ExteriorAlgebra.ιMulti ℝ d w)
    rw [ExteriorAlgebra.map_apply_ιMulti]
    simp only [evaluateForm, ExteriorAlgebra.liftAlternating_apply_ιMulti]
    by_cases hd : d = k
    · subst d
      simp only [dite_true]
      change Matrix.det (fun i j => ∑ l, covectorPullback A (w i) l * v j l) =
        Matrix.det (fun i j => ∑ l, w i l * A (v j) l)
      congr 1
      funext i j
      exact covectorPullback_pairing A (w i) (v j)
    · simp [hd]
  exact congrArg (fun L : CotangentExterior m →ₗ[ℝ] ℝ => L a) he

lemma ParameterDomain.integral_congr {k : ℕ} {D : ParameterDomain k}
    {f g : Coord k → ℝ} (hf : ContinuousOn f D.carrier)
    (hg : ContinuousOn g D.carrier) (he : EqOn f g D.carrier) :
    D.integral f = D.integral g := by
  rw [D.integral_eq_setIntegral hf, D.integral_eq_setIntegral hg]
  exact setIntegral_congr_fun D.isClosed.measurableSet he

lemma Surface.differentiableAt {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) {u : Coord k} (hu : u ∈ Φ.domain.carrier) :
    DifferentiableAt ℝ Φ.map u :=
  (Φ.regularity.differentiableOn (by norm_num)).differentiableAt
    (Φ.open_neighborhood.mem_nhds (Φ.domain_subset hu))

lemma surfaceIntegrand_mapBy {k n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (Φ : Surface k n E) (T : Euclidean n → Euclidean m)
    (hE : IsOpen E) (hT : ContDiffOn ℝ 1 T E) (hTV : MapsTo T E V)
    (ω : FormField m) :
    EqOn (surfaceIntegrand (Φ.mapBy T hE hT hTV) ω)
      (surfaceIntegrand Φ (pullbackForm T ω)) Φ.domain.carrier := by
  intro u hu
  have hΦ := Φ.differentiableAt hu
  have hTx := (hT.differentiableOn (by norm_num)).differentiableAt (hE.mem_nhds (Φ.mapsTo hu))
  change evaluateForm k (fun j => fderiv ℝ (T ∘ Φ.map) u (Pi.single j 1))
    (ω (T (Φ.map u))) = evaluateForm k (fun j => fderiv ℝ Φ.map u (Pi.single j 1))
      (ExteriorAlgebra.map (covectorPullback (fderiv ℝ T (Φ.map u))) (ω (T (Φ.map u))))
  rw [evaluateForm_pullback, fderiv_comp u hTx hΦ]
  rfl

lemma surfaceIntegrand_identity_pullback {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (ω : FormField n) :
    EqOn (surfaceIntegrand (identityParameterSurface Φ.domain) (pullbackForm Φ.euclideanMap ω))
      (surfaceIntegrand Φ ω) Φ.domain.carrier := by
  intro u hu
  have hΦ := Φ.differentiableAt hu
  have he : HasFDerivAt Φ.euclideanMap
      ((fderiv ℝ Φ.map u).comp (coordEquivEuclidean k).symm.toContinuousLinearMap)
      (coordEquivEuclidean k u) := by
    simpa only [Surface.euclideanMap, ContinuousLinearEquiv.symm_apply_apply] using
      hΦ.hasFDerivAt.comp (coordEquivEuclidean k u)
        ((coordEquivEuclidean k).symm.hasFDerivAt)
  change evaluateForm k (fun j => fderiv ℝ (coordEquivEuclidean k) u (Pi.single j 1))
      (ExteriorAlgebra.map (covectorPullback (fderiv ℝ Φ.euclideanMap (coordEquivEuclidean k u)))
        (ω (Φ.euclideanMap (coordEquivEuclidean k u)))) = _
  rw [evaluateForm_pullback, he.fderiv, (coordEquivEuclidean k).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, Surface.euclideanMap, Function.comp_apply]
  rfl

end Rudin.PMA.Chapter10
