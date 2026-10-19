import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_17 (bit : Fin 16) :
    row (16*17+bit.val) < 1024 ∧
      groupMask (group ⟨17,by decide⟩) bit = inactive (16*17+bit.val) := by
  fin_cases bit <;> decide

theorem block_18 (bit : Fin 16) :
    row (16*18+bit.val) < 1024 ∧
      groupMask (group ⟨18,by decide⟩) bit = inactive (16*18+bit.val) := by
  fin_cases bit <;> decide

theorem block_19 (bit : Fin 16) :
    row (16*19+bit.val) < 1024 ∧
      groupMask (group ⟨19,by decide⟩) bit = inactive (16*19+bit.val) := by
  fin_cases bit <;> decide

theorem block_20 (bit : Fin 16) :
    row (16*20+bit.val) < 1024 ∧
      groupMask (group ⟨20,by decide⟩) bit = inactive (16*20+bit.val) := by
  fin_cases bit <;> decide

theorem block_21 (bit : Fin 16) :
    row (16*21+bit.val) < 1024 ∧
      groupMask (group ⟨21,by decide⟩) bit = inactive (16*21+bit.val) := by
  fin_cases bit <;> decide

theorem block_22 (bit : Fin 16) :
    row (16*22+bit.val) < 1024 ∧
      groupMask (group ⟨22,by decide⟩) bit = inactive (16*22+bit.val) := by
  fin_cases bit <;> decide

theorem block_23 (bit : Fin 16) :
    row (16*23+bit.val) < 1024 ∧
      groupMask (group ⟨23,by decide⟩) bit = inactive (16*23+bit.val) := by
  fin_cases bit <;> decide

theorem block_24 (bit : Fin 16) :
    row (16*24+bit.val) < 1024 ∧
      groupMask (group ⟨24,by decide⟩) bit = inactive (16*24+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_17
#print axioms block_18
#print axioms block_19
#print axioms block_20
#print axioms block_21
#print axioms block_22
#print axioms block_23
#print axioms block_24
end AspisR1.CuSavingsS2Tables
