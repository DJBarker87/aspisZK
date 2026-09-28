/- Compose the current polynomial core with the retained rational circle
   normalization. Explicit domain/good-minor conditions, no sampler law. -/
import AspisV8R19.SparseGPolynomial
import AspisV8R17.NormalizedChord

namespace AspisR19.SparseGAdmissible
open AspisV8R17 AspisR19.SparseGPolynomial MvPolynomial
variable {F : Type*} [Field F]

theorem source_chord_scale (half t a b c : F) (q : Nat → F) (r : Nat) :
    sourceChord half q (t*a) (t*b) (t*c) r = t*sourceChord half q a b c r := by
  unfold sourceChord finiteChordCoefficient
  split <;> simp only [finiteChordEven,finiteChordOdd] <;> ring

theorem entry_scale (half alpha t a b c : F) (i j : Fin 271) :
    entry half alpha (t*a) (t*b) (t*c) i j = t*entry half alpha a b c i j := by
  exact source_chord_scale _ _ _ _ _ _ _

theorem minor_mulVec_scale (half alpha t a b c : F) (w : Fin 271 → F) :
    (minor half alpha (t*a) (t*b) (t*c)).mulVec w =
      fun i => t*(minor half alpha a b c).mulVec w i := by
  funext i
  simp only [Matrix.mulVec,dotProduct,minor,entry_scale,mul_assoc,Finset.mul_sum]

theorem admissible_core_surjective (half alpha u v : F)
    (h2 : (2:F)≠0) (hu : 1+u^2≠0) (hv : 1+v^2≠0) (hne : v≠u)
    (good : eval (activeAssignment alpha u v) (polyMinor half).det ≠ 0) :
    Function.Surjective
      (minor half alpha
        (rationalX u*rationalY v-rationalY u*rationalX v)
        (rationalY u-rationalY v) (rationalX v-rationalX u)).mulVec := by
  obtain ⟨ha,hb,hc⟩ := rational_chord_normalization u v hu hv
  rw [ha,hb,hc]
  have hs := chordScale_ne_zero u v h2 hu hv hne
  intro target
  obtain ⟨w,hw⟩ := core_surjective_outside_zero_set half alpha u v good
    (fun i => target i/chordScale u v)
  refine ⟨w,?_⟩
  rw [minor_mulVec_scale,hw]
  funext i
  exact mul_div_cancel₀ (target i) hs

#print axioms source_chord_scale
#print axioms entry_scale
#print axioms minor_mulVec_scale
#print axioms admissible_core_surjective
end AspisR19.SparseGAdmissible
