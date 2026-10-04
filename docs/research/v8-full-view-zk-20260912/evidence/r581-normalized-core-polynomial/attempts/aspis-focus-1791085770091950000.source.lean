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
  ext i j
  change eval (circleAssignment alpha u v)
      (eval₂ (C : F →+* Poly F) substitution (coreEntryPolynomial half i j)) = _
  let ev : Poly F →+* F := eval (circleAssignment alpha u v)
  have hcomp : ev.comp (eval₂Hom (C : F →+* Poly F) substitution) =
      eval₂Hom (RingHom.id F) (fun k => ev (substitution k)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ev]
    · intro k
      simp [ev]
  have h := congrArg (fun f : Poly F →+* F => f (coreEntryPolynomial half i j)) hcomp
  change eval (circleAssignment alpha u v)
      (eval₂ (C : F →+* Poly F) substitution (coreEntryPolynomial half i j)) = _ at h
  rw [← h]
  have hvalues : (fun k => ev (substitution k)) =
      coreAssignment alpha (1+u*v) (u*v-1) (-(u+v)) := by
    funext k
    fin_cases k <;> simp [ev, substitution, circleAssignment, coreAssignment] <;> ring
  rw [hvalues]
  simpa [eval₂] using coreEntryPolynomial_eval half alpha (1+u*v) (u*v-1) (-(u+v)) i j

theorem normalizedPolynomialDet_eval (half alpha u v : F) :
    eval (circleAssignment alpha u v) (normalizedPolynomialMatrix half).det =
      (coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v))).det := by
  rw [(eval (circleAssignment alpha u v)).map_det, normalizedPolynomialMatrix_eval]

theorem normalizedPolynomialDet_ne_zero (half : F) (hi : ∃ z : F, z*z = -1) :
    (normalizedPolynomialMatrix half).det ≠ 0 := by
  obtain ⟨z, hz⟩ := hi
  have hz1 : z * (-z) = 1 := by rw [mul_neg, hz, neg_neg]
  have hcoords : (1 + z * (-z), z * (-z) - 1, -(z + (-z))) = ((2:F),0,0) := by
    rw [hz1]
    ring
  have he := normalizedPolynomialDet_eval half 1 z (-z)
  rw [hzero, map_zero] at he
  rw [hcoords] at he
  exact coreMatrix_witness_det_ne_zero half he.symm
  exact coreMatrix_witness_det_ne_zero half he.symm

end AspisV8R19.R581NormalizedCorePolynomial
