import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_49 (bit : Fin 16) :
    row (16*49+bit.val) < 1024 ∧
      groupMask (group ⟨49,by decide⟩) bit = inactive (16*49+bit.val) := by
  fin_cases bit <;> decide

theorem block_50 (bit : Fin 16) :
    row (16*50+bit.val) < 1024 ∧
      groupMask (group ⟨50,by decide⟩) bit = inactive (16*50+bit.val) := by
  fin_cases bit <;> decide

theorem block_51 (bit : Fin 16) :
    row (16*51+bit.val) < 1024 ∧
      groupMask (group ⟨51,by decide⟩) bit = inactive (16*51+bit.val) := by
  fin_cases bit <;> decide

theorem block_52 (bit : Fin 16) :
    row (16*52+bit.val) < 1024 ∧
      groupMask (group ⟨52,by decide⟩) bit = inactive (16*52+bit.val) := by
  fin_cases bit <;> decide

theorem block_53 (bit : Fin 16) :
    row (16*53+bit.val) < 1024 ∧
      groupMask (group ⟨53,by decide⟩) bit = inactive (16*53+bit.val) := by
  fin_cases bit <;> decide

theorem block_54 (bit : Fin 16) :
    row (16*54+bit.val) < 1024 ∧
      groupMask (group ⟨54,by decide⟩) bit = inactive (16*54+bit.val) := by
  fin_cases bit <;> decide

theorem block_55 (bit : Fin 16) :
    row (16*55+bit.val) < 1024 ∧
      groupMask (group ⟨55,by decide⟩) bit = inactive (16*55+bit.val) := by
  fin_cases bit <;> decide

theorem block_56 (bit : Fin 16) :
    row (16*56+bit.val) < 1024 ∧
      groupMask (group ⟨56,by decide⟩) bit = inactive (16*56+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_49
#print axioms block_50
#print axioms block_51
#print axioms block_52
#print axioms block_53
#print axioms block_54
#print axioms block_55
#print axioms block_56
end AspisR1.CuSavingsS2Tables
