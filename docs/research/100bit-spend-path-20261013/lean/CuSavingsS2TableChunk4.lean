import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_25 (bit : Fin 16) :
    row (16*25+bit.val) < 1024 ∧
      groupMask (group ⟨25,by decide⟩) bit = inactive (16*25+bit.val) := by
  fin_cases bit <;> decide

theorem block_26 (bit : Fin 16) :
    row (16*26+bit.val) < 1024 ∧
      groupMask (group ⟨26,by decide⟩) bit = inactive (16*26+bit.val) := by
  fin_cases bit <;> decide

theorem block_27 (bit : Fin 16) :
    row (16*27+bit.val) < 1024 ∧
      groupMask (group ⟨27,by decide⟩) bit = inactive (16*27+bit.val) := by
  fin_cases bit <;> decide

theorem block_28 (bit : Fin 16) :
    row (16*28+bit.val) < 1024 ∧
      groupMask (group ⟨28,by decide⟩) bit = inactive (16*28+bit.val) := by
  fin_cases bit <;> decide

theorem block_29 (bit : Fin 16) :
    row (16*29+bit.val) < 1024 ∧
      groupMask (group ⟨29,by decide⟩) bit = inactive (16*29+bit.val) := by
  fin_cases bit <;> decide

theorem block_30 (bit : Fin 16) :
    row (16*30+bit.val) < 1024 ∧
      groupMask (group ⟨30,by decide⟩) bit = inactive (16*30+bit.val) := by
  fin_cases bit <;> decide

theorem block_31 (bit : Fin 16) :
    row (16*31+bit.val) < 1024 ∧
      groupMask (group ⟨31,by decide⟩) bit = inactive (16*31+bit.val) := by
  fin_cases bit <;> decide

theorem block_32 (bit : Fin 16) :
    row (16*32+bit.val) < 1024 ∧
      groupMask (group ⟨32,by decide⟩) bit = inactive (16*32+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_25
#print axioms block_26
#print axioms block_27
#print axioms block_28
#print axioms block_29
#print axioms block_30
#print axioms block_31
#print axioms block_32
end AspisR1.CuSavingsS2Tables
