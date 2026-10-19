import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_57 (bit : Fin 16) :
    row (16*57+bit.val) < 1024 ∧
      groupMask (group ⟨57,by decide⟩) bit = inactive (16*57+bit.val) := by
  fin_cases bit <;> decide

theorem block_58 (bit : Fin 16) :
    row (16*58+bit.val) < 1024 ∧
      groupMask (group ⟨58,by decide⟩) bit = inactive (16*58+bit.val) := by
  fin_cases bit <;> decide

theorem block_59 (bit : Fin 16) :
    row (16*59+bit.val) < 1024 ∧
      groupMask (group ⟨59,by decide⟩) bit = inactive (16*59+bit.val) := by
  fin_cases bit <;> decide

theorem block_60 (bit : Fin 16) :
    row (16*60+bit.val) < 1024 ∧
      groupMask (group ⟨60,by decide⟩) bit = inactive (16*60+bit.val) := by
  fin_cases bit <;> decide

theorem block_61 (bit : Fin 16) :
    row (16*61+bit.val) < 1024 ∧
      groupMask (group ⟨61,by decide⟩) bit = inactive (16*61+bit.val) := by
  fin_cases bit <;> decide

theorem block_62 (bit : Fin 16) :
    row (16*62+bit.val) < 1024 ∧
      groupMask (group ⟨62,by decide⟩) bit = inactive (16*62+bit.val) := by
  fin_cases bit <;> decide

theorem block_63 (bit : Fin 16) :
    row (16*63+bit.val) < 1024 ∧
      groupMask (group ⟨63,by decide⟩) bit = inactive (16*63+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_57
#print axioms block_58
#print axioms block_59
#print axioms block_60
#print axioms block_61
#print axioms block_62
#print axioms block_63
end AspisR1.CuSavingsS2Tables
