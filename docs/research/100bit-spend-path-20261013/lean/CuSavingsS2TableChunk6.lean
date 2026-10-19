import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_41 (bit : Fin 16) :
    row (16*41+bit.val) < 1024 ∧
      groupMask (group ⟨41,by decide⟩) bit = inactive (16*41+bit.val) := by
  fin_cases bit <;> decide

theorem block_42 (bit : Fin 16) :
    row (16*42+bit.val) < 1024 ∧
      groupMask (group ⟨42,by decide⟩) bit = inactive (16*42+bit.val) := by
  fin_cases bit <;> decide

theorem block_43 (bit : Fin 16) :
    row (16*43+bit.val) < 1024 ∧
      groupMask (group ⟨43,by decide⟩) bit = inactive (16*43+bit.val) := by
  fin_cases bit <;> decide

theorem block_44 (bit : Fin 16) :
    row (16*44+bit.val) < 1024 ∧
      groupMask (group ⟨44,by decide⟩) bit = inactive (16*44+bit.val) := by
  fin_cases bit <;> decide

theorem block_45 (bit : Fin 16) :
    row (16*45+bit.val) < 1024 ∧
      groupMask (group ⟨45,by decide⟩) bit = inactive (16*45+bit.val) := by
  fin_cases bit <;> decide

theorem block_46 (bit : Fin 16) :
    row (16*46+bit.val) < 1024 ∧
      groupMask (group ⟨46,by decide⟩) bit = inactive (16*46+bit.val) := by
  fin_cases bit <;> decide

theorem block_47 (bit : Fin 16) :
    row (16*47+bit.val) < 1024 ∧
      groupMask (group ⟨47,by decide⟩) bit = inactive (16*47+bit.val) := by
  fin_cases bit <;> decide

theorem block_48 (bit : Fin 16) :
    row (16*48+bit.val) < 1024 ∧
      groupMask (group ⟨48,by decide⟩) bit = inactive (16*48+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_41
#print axioms block_42
#print axioms block_43
#print axioms block_44
#print axioms block_45
#print axioms block_46
#print axioms block_47
#print axioms block_48
end AspisR1.CuSavingsS2Tables
