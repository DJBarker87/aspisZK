import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_1 (bit : Fin 16) :
    row (16*1+bit.val) < 1024 ∧
      groupMask (group ⟨1,by decide⟩) bit = inactive (16*1+bit.val) := by
  fin_cases bit <;> decide

theorem block_2 (bit : Fin 16) :
    row (16*2+bit.val) < 1024 ∧
      groupMask (group ⟨2,by decide⟩) bit = inactive (16*2+bit.val) := by
  fin_cases bit <;> decide

theorem block_3 (bit : Fin 16) :
    row (16*3+bit.val) < 1024 ∧
      groupMask (group ⟨3,by decide⟩) bit = inactive (16*3+bit.val) := by
  fin_cases bit <;> decide

theorem block_4 (bit : Fin 16) :
    row (16*4+bit.val) < 1024 ∧
      groupMask (group ⟨4,by decide⟩) bit = inactive (16*4+bit.val) := by
  fin_cases bit <;> decide

theorem block_5 (bit : Fin 16) :
    row (16*5+bit.val) < 1024 ∧
      groupMask (group ⟨5,by decide⟩) bit = inactive (16*5+bit.val) := by
  fin_cases bit <;> decide

theorem block_6 (bit : Fin 16) :
    row (16*6+bit.val) < 1024 ∧
      groupMask (group ⟨6,by decide⟩) bit = inactive (16*6+bit.val) := by
  fin_cases bit <;> decide

theorem block_7 (bit : Fin 16) :
    row (16*7+bit.val) < 1024 ∧
      groupMask (group ⟨7,by decide⟩) bit = inactive (16*7+bit.val) := by
  fin_cases bit <;> decide

theorem block_8 (bit : Fin 16) :
    row (16*8+bit.val) < 1024 ∧
      groupMask (group ⟨8,by decide⟩) bit = inactive (16*8+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_1
#print axioms block_2
#print axioms block_3
#print axioms block_4
#print axioms block_5
#print axioms block_6
#print axioms block_7
#print axioms block_8
end AspisR1.CuSavingsS2Tables
