import AspisV8R19.FixedQueryPolynomial
import AspisV8R19.ResidualHomogeneous

/-! Full-support homogeneity, including sparse G. Actual rational chord
coordinates have the same nonsingularity condition when their scale is nonzero. -/
namespace AspisR19.FixedQueryChordScale
open AspisV8R17 FixedQueryModel HighRepairInvariant BetaUniformCorrection
noncomputable section
variable {F : Type*} [CommRing F]

theorem point_scale (half scale a b c : F) (z : Fin 10 → F) (which : Nat) (i : Index 32) :
    pointWeight half (scale*a) (scale*b) (scale*c) z which i=
      scale*pointWeight half a b c z which i := by
  simp only [pointWeight,FullQuotientWeights.pointWeight,ResidualHomogeneous.chord_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem g_scale (half scale a b c : F) (i : Index 32) :
    gBoundary half (scale*a) (scale*b) (scale*c) i=scale*gBoundary half a b c i := by
  simp only [gBoundary,ResidualHomogeneous.chord_scale]
  ring

theorem weight_scale (half scale a b c kappa : F) (z : Fin 10 → F) (structured : Bool) (i : Index 32) :
    weight half (scale*a) (scale*b) (scale*c) kappa z structured i=
      scale*weight half a b c kappa z structured i := by
  cases structured <;> simp only [weight,point_scale,g_scale,Bool.false_eq_true,if_false,if_true] <;> ring

theorem coefficient_scale (quarter scale : F) (q w : Index 32 → F) (k : Nat) :
    coefficient (sourceKernel 32 k quarter) q (fun i => scale*w i)=
      scale*coefficient (sourceKernel 32 k quarter) q w := by
  have h := coefficient_right (sourceKernel 32 k quarter) q w (fun _ => 0) scale 0
  simpa only [zero_mul,add_zero,zero_mul,add_zero] using h

theorem observation_scale (half quarter scale a b c kappa : F) (z : Fin 10 → F)
    (q : Index 32 → F) (row : Nat) :
    observed half quarter (scale*a) (scale*b) (scale*c) kappa z q row=
      scale*observed half quarter a b c kappa z q row := by
  unfold observed
  split_ifs
  · simp only [point_scale,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [funext (weight_scale half scale a b c kappa z false),coefficient_scale]
  · rw [funext (weight_scale half scale a b c kappa z true),coefficient_scale]

theorem determinant_scale (half quarter scale a b c kappa alpha : F) (z : Fin 10 → F)
    (v : Fin 13 → Fin 32 → F) :
    (matrix half quarter (scale*a) (scale*b) (scale*c) kappa alpha z v).det=
      scale^13*(matrix half quarter a b c kappa alpha z v).det := by
  have hm : matrix half quarter (scale*a) (scale*b) (scale*c) kappa alpha z v=
      scale • matrix half quarter a b c kappa alpha z v := by
    ext i j
    exact observation_scale half quarter scale a b c kappa z _ _
  rw [hm,Matrix.det_smul]
  simp

theorem rational_determinant {K : Type*} [Field K] (half quarter kappa alpha u v : K)
    (z : Fin 10 → K) (sectionValues : Fin 13 → Fin 32 → K)
    (hu : 1+u^2≠0) (hv : 1+v^2≠0) :
    (matrix half quarter
      (rationalX u*rationalY v-rationalY u*rationalX v)
      (rationalY u-rationalY v) (rationalX v-rationalX u) kappa alpha z sectionValues).det=
      chordScale u v^13*(FixedQueryPolynomial.normalizedMatrix half quarter kappa alpha u v z sectionValues).det := by
  obtain ⟨ha,hb,hc⟩ := rational_chord_normalization u v hu hv
  rw [ha,hb,hc,determinant_scale]
  rfl

theorem rational_nonzero_iff {K : Type*} [Field K] (half quarter kappa alpha u v : K)
    (z : Fin 10 → K) (sectionValues : Fin 13 → Fin 32 → K)
    (h2 : (2:K)≠0) (hu : 1+u^2≠0) (hv : 1+v^2≠0) (hne : v≠u) :
    (matrix half quarter
      (rationalX u*rationalY v-rationalY u*rationalX v)
      (rationalY u-rationalY v) (rationalX v-rationalX u) kappa alpha z sectionValues).det≠0 ↔
      (FixedQueryPolynomial.normalizedMatrix half quarter kappa alpha u v z sectionValues).det≠0 := by
  rw [rational_determinant half quarter kappa alpha u v z sectionValues hu hv]
  have hs := chordScale_ne_zero u v h2 hu hv hne
  simp [hs]

#print axioms point_scale
#print axioms g_scale
#print axioms weight_scale
#print axioms coefficient_scale
#print axioms observation_scale
#print axioms determinant_scale
#print axioms rational_determinant
#print axioms rational_nonzero_iff
end
end AspisR19.FixedQueryChordScale
