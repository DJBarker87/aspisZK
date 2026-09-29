/- Generated staged point-weight certificate. Do not inline earlier stages. -/
import AspisV8R19.WitnessPointData
namespace AspisR19.WitnessPointData
open RootCertificate ResidualModel
noncomputable section
theorem chord_support12 : ∀ j : Fin 111, j ∉ ({12,13,14}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 12 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support12
theorem chord_support13 : ∀ j : Fin 111, j ∉ ({0,8,12,13,15,16}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 13 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support13
theorem chord_support14 : ∀ j : Fin 111, j ∉ ({0,8,12,14,15,16}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 14 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support14
theorem chord_support15 : ∀ j : Fin 111, j ∉ ({1,2,9,10,13,14,15,17,18}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 15 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support15
theorem chord_support16 : ∀ j : Fin 111, j ∉ ({16,17,18}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 16 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support16
theorem chord_support17 : ∀ j : Fin 111, j ∉ ({16,17,19,20}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 17 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support17
theorem chord_support18 : ∀ j : Fin 111, j ∉ ({16,18,19,20}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 18 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support18
theorem chord_support19 : ∀ j : Fin 111, j ∉ ({17,18,19,21,22}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 19 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support19
theorem chord_support20 : ∀ j : Fin 111, j ∉ ({20,21,22}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 20 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support20
theorem chord_support21 : ∀ j : Fin 111, j ∉ ({16,20,21,23,24}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 21 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support21
theorem chord_support22 : ∀ j : Fin 111, j ∉ ({16,20,22,23,24}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 22 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support22
theorem chord_support23 : ∀ j : Fin 111, j ∉ ({17,18,21,22,23,25,26}:Finset (Fin 111)) → chordEntry half (7:M) 5 (-5) 23 j.val = 0 := by
  intro j
  fin_cases j <;> decide
#print axioms chord_support23
end
end AspisR19.WitnessPointData
