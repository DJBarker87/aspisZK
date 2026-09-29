/- Small literal contractions, with source slot order retained. -/
import AspisV8R19.PointWeightCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace AspisR19.ResidualEntryCertificate
open ResidualModel RootCertificate
variable {F : Type*} [CommRing F]
noncomputable section

theorem sum108 (f : Fin 108 → F) :
    (∑ r, f r) =
      (∑ j : Fin 27, f ⟨j.val,by omega⟩) +
      ((∑ j : Fin 27, f ⟨27+j.val,by omega⟩) +
      ((∑ j : Fin 27, f ⟨54+j.val,by omega⟩) +
       (∑ j : Fin 27, f ⟨81+j.val,by omega⟩))) := by
  rw [Fin.sum_univ_add (a:=27) (b:=81)]
  rw [Fin.sum_univ_add (a:=27) (b:=54)]
  rw [Fin.sum_univ_add (a:=27) (b:=27)]
  rfl

def polySlot (quarter : F) (q w : Fin 108 → F) (b : Fin 27) (k : Fin 7) : F :=
  let q0 := q ⟨4*b.val,by omega⟩
  let q1 := q ⟨4*b.val+1,by omega⟩
  let q2 := q ⟨4*b.val+2,by omega⟩
  let q3 := q ⟨4*b.val+3,by omega⟩
  let w0 := w ⟨4*b.val,by omega⟩
  let w1 := w ⟨4*b.val+1,by omega⟩
  let w2 := w ⟨4*b.val+2,by omega⟩
  let w3 := w ⟨4*b.val+3,by omega⟩
  [quarter*q0*w0,
   quarter*q0*w3+quarter*q1*w0,
   quarter*q0*w2+quarter*q1*w3+quarter*q2*w0,
   quarter*q0*w1+quarter*q1*w2+quarter*q2*w3+quarter*q3*w0,
   quarter*q1*w1+quarter*q2*w2+quarter*q3*w3,
   quarter*q2*w1+quarter*q3*w2,
   quarter*q3*w1].getD k.val 0

theorem poly_slots (quarter : F) (q w : Fin 108 → F) (k : Fin 7) :
    polyCoeff quarter q w k.val = ∑ b : Fin 27, polySlot quarter q w b k := by
  fin_cases k <;> simp [polyCoeff, polySlot, Fin.sum_univ_four, add_assoc]

#print axioms sum108
#print axioms poly_slots
end
end AspisR19.ResidualEntryCertificate
