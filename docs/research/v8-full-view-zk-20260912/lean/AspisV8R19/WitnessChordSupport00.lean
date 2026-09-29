/- Generated staged point-weight certificate. Do not inline earlier stages. -/
import AspisV8R19.WitnessPointData
namespace AspisR19.WitnessPointData
open RootCertificate ResidualModel
noncomputable section
theorem chord_support0 : ∀ j : Fin 111, j ∉ ({0,1,2}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 0 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support0
theorem chord_support1 : ∀ j : Fin 111, j ∉ ({0,1,3,4}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 1 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support1
theorem chord_support2 : ∀ j : Fin 111, j ∉ ({0,2,3,4}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 2 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support2
theorem chord_support3 : ∀ j : Fin 111, j ∉ ({1,2,3,5,6}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 3 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support3
theorem chord_support4 : ∀ j : Fin 111, j ∉ ({4,5,6}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 4 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support4
theorem chord_support5 : ∀ j : Fin 111, j ∉ ({0,4,5,7,8}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 5 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support5
theorem chord_support6 : ∀ j : Fin 111, j ∉ ({0,4,6,7,8}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 6 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support6
theorem chord_support7 : ∀ j : Fin 111, j ∉ ({1,2,5,6,7,9,10}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 7 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support7
theorem chord_support8 : ∀ j : Fin 111, j ∉ ({8,9,10}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 8 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support8
theorem chord_support9 : ∀ j : Fin 111, j ∉ ({8,9,11,12}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 9 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support9
theorem chord_support10 : ∀ j : Fin 111, j ∉ ({8,10,11,12}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 10 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support10
theorem chord_support11 : ∀ j : Fin 111, j ∉ ({9,10,11,13,14}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 11 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support11
end
end AspisR19.WitnessPointData
