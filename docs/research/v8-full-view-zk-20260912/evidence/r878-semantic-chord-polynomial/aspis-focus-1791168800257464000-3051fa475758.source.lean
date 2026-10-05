import AspisV8R19.R837ActiveJointEntryDegree

set_option autoImplicit false
namespace AspisV8R19.R878SemanticChordPolynomial
open MvPolynomial AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R837ActiveJointEntryDegree
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- The same exact source-chord polynomial, at an arbitrary source code. -/
def chordPolynomial (half : F) (d : Fin 255) (s : Fin 3) (r : Nat) : JointPoly F :=
  ∑ l : Fin 3, polynomialABC l *
    (C (sourceBasisConstants half (qdiff d s) r l) -
      pAlpha^(s.val+1) * C (sourceBasisConstants half (sdiff d) r l))

theorem eval_chordPolynomial (half alpha u v kappa tau : F) (z : Fin 10 → F)
    (d : Fin 255) (s : Fin 3) (r : Nat) :
    eval (assignment alpha u v kappa tau z) (chordPolynomial half d s r) =
      sourceChord half (direction alpha d s) (1+u*v) (u*v-1) (-(u+v)) r := by
  have hα : assignment alpha u v kappa tau z 0 = alpha := rfl
  have hu : assignment alpha u v kappa tau z 1 = u := rfl
  have hv : assignment alpha u v kappa tau z 2 = v := rfl
  unfold chordPolynomial
  rw [Fin.sum_univ_succ]
  simp [polynomialABC, pAlpha, pU, pV, hα, hu, hv]
  have hq : (fun i => qdiff d s i-alpha^(s.val+1)*sdiff d i) = direction alpha d s := by
    funext i
    unfold qdiff AspisV8R19.R745JointObservationPolynomial.sdiff direction qPair
    simp only [Fin.val_zero, Nat.mul_zero, zero_add]
    ring
  rw [← hq]
  calc
    _ = (1+u*v) *
          (sourceChord half (qdiff d s) 1 0 0 r -
            alpha^(s.val+1) * sourceChord half (sdiff d) 1 0 0 r) +
        (u*v-1) *
          (sourceChord half (qdiff d s) 0 1 0 r -
            alpha^(s.val+1) * sourceChord half (sdiff d) 0 1 0 r) +
        (-(u+v)) *
          (sourceChord half (qdiff d s) 0 0 1 r -
            alpha^(s.val+1) * sourceChord half (sdiff d) 0 0 1 r) := by
              simp [sourceBasisConstants]
              ring
    _ = _ := (sourceChord_six_constants half (qdiff d s) (sdiff d)
      (1+u*v) (u*v-1) (-(u+v)) (alpha^(s.val+1)) r).symm.trans (by
        congr 2 <;> ring)

theorem chordPolynomial_totalDegree_le (half : F) (d : Fin 255) (s : Fin 3) (r : Nat) :
    (chordPolynomial half d s r).totalDegree ≤ 5 := by
  unfold chordPolynomial
  apply totalDegree_finsetSum_le
  intro l _
  have hp : (pAlpha ^ (s.val+1) : JointPoly F).totalDegree ≤ 3 := by
    have h := totalDegree_pow (X (0 : Fin 15) : JointPoly F) (s.val+1)
    exact h.trans (by have := s.isLt; simp only [totalDegree_X]; omega)
  have hshift : (pAlpha^(s.val+1) * C (sourceBasisConstants half (sdiff d) r l) :
      JointPoly F).totalDegree ≤ 3 :=
    (totalDegree_mul _ _).trans (by simpa using hp)
  have hc : (C (sourceBasisConstants half (qdiff d s) r l) : JointPoly F).totalDegree ≤ 0 := by simp
  have hb : (C (sourceBasisConstants half (qdiff d s) r l) -
      pAlpha^(s.val+1)*C (sourceBasisConstants half (sdiff d) r l) : JointPoly F).totalDegree ≤ 3 :=
    (totalDegree_sub _ _).trans (max_le (hc.trans (by decide)) hshift)
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (polynomialABC_totalDegree_le l) hb)

#print axioms eval_chordPolynomial
#print axioms chordPolynomial_totalDegree_le
end
end AspisV8R19.R878SemanticChordPolynomial
