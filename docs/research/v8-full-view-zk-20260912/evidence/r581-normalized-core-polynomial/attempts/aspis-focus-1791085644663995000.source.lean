import AspisV8R19.R574SparseGCorePolynomial
import AspisV8R17.MinorDegree

set_option autoImplicit false
namespace AspisV8R19.R581NormalizedCorePolynomial

open MvPolynomial AspisV8R19.R574SparseGCorePolynomial

variable {F : Type*} [Field F] [NeZero (2 : F)]

abbrev Poly (F : Type*) [CommSemiring F] := MvPolynomial (Fin 3) F

def circleAssignment (alpha u v : F) : Fin 3 → F :=
  fun i => if i.val = 0 then alpha else if i.val = 1 then u else v

def normalizedChordAssignment (u v : F) : Fin 4 → F :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then 1 + u*v
    else if i.val = 2 then u*v - 1 else -(u+v)

noncomputable def substitution : Fin 4 → Poly F := fun i =>
  if i.val = 0 then X (0 : Fin 3)
  else if i.val = 1 then 1 + X (1 : Fin 3) * X (2 : Fin 3)
  else if i.val = 2 then X (1 : Fin 3) * X (2 : Fin 3) - 1
  else -(X (1 : Fin 3) + X (2 : Fin 3))

noncomputable def substitute (p : MvPolynomial (Fin 4) F) : Poly F :=
  eval₂ (C : F →+* Poly F) substitution p

noncomputable def normalizedPolynomialMatrix (half : F) : Matrix (Fin 271) (Fin 271) (Poly F) :=
  fun i j => substitute (corePolynomialMatrix half i j)

theorem normalizedPolynomialMatrix_eval (half alpha u v : F) :
    (eval (circleAssignment alpha u v)).mapMatrix (normalizedPolynomialMatrix half) =
      coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v)) := by
  sorry

theorem normalizedPolynomialDet_eval (half alpha u v : F) :
    eval (circleAssignment alpha u v) (normalizedPolynomialMatrix half).det =
      (coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v))).det := by
  rw [(eval (circleAssignment alpha u v)).map_det, normalizedPolynomialMatrix_eval]

theorem normalizedPolynomialDet_ne_zero (half : F) (hi : ∃ z : F, z*z = -1) :
    (normalizedPolynomialMatrix half).det ≠ 0 := by
  intro hzero
  obtain ⟨z, hz⟩ := hi
  have hch := AspisR19.SparseGCoreInverse.normalized_chord z hz
  have he := normalizedPolynomialDet_eval half 1 z (-z)
  rw [hzero, map_zero] at he
  sorry
  exact coreMatrix_witness_det_ne_zero half he.symm

end AspisV8R19.R581NormalizedCorePolynomial

#check MvPolynomial.eval₂Hom_comp
#check MvPolynomial.eval₂Hom_apply
#check MvPolynomial.eval₂Hom_X
#check MvPolynomial.eval₂_eq_eval_map
#check MvPolynomial.eval₂Hom_comp_eval
#check MvPolynomial.eval₂_comp
