import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_9 (bit : Fin 16) :
    row (16*9+bit.val) < 1024 ∧
      groupMask (group ⟨9,by decide⟩) bit = inactive (16*9+bit.val) := by
  fin_cases bit <;> decide

theorem block_10 (bit : Fin 16) :
    row (16*10+bit.val) < 1024 ∧
      groupMask (group ⟨10,by decide⟩) bit = inactive (16*10+bit.val) := by
  fin_cases bit <;> decide

theorem block_11 (bit : Fin 16) :
    row (16*11+bit.val) < 1024 ∧
      groupMask (group ⟨11,by decide⟩) bit = inactive (16*11+bit.val) := by
  fin_cases bit <;> decide

theorem block_12 (bit : Fin 16) :
    row (16*12+bit.val) < 1024 ∧
      groupMask (group ⟨12,by decide⟩) bit = inactive (16*12+bit.val) := by
  fin_cases bit <;> decide

theorem block_13 (bit : Fin 16) :
    row (16*13+bit.val) < 1024 ∧
      groupMask (group ⟨13,by decide⟩) bit = inactive (16*13+bit.val) := by
  fin_cases bit <;> decide

theorem block_14 (bit : Fin 16) :
    row (16*14+bit.val) < 1024 ∧
      groupMask (group ⟨14,by decide⟩) bit = inactive (16*14+bit.val) := by
  fin_cases bit <;> decide

theorem block_15 (bit : Fin 16) :
    row (16*15+bit.val) < 1024 ∧
      groupMask (group ⟨15,by decide⟩) bit = inactive (16*15+bit.val) := by
  fin_cases bit <;> decide

theorem block_16 (bit : Fin 16) :
    row (16*16+bit.val) < 1024 ∧
      groupMask (group ⟨16,by decide⟩) bit = inactive (16*16+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_9
#print axioms block_10
#print axioms block_11
#print axioms block_12
#print axioms block_13
#print axioms block_14
#print axioms block_15
#print axioms block_16
end AspisR1.CuSavingsS2Tables
