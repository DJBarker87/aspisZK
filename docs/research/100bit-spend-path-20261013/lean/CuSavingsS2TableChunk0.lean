import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_0 (bit : Fin 16) :
    row (16*0+bit.val) < 1024 ∧
      groupMask (group ⟨0,by decide⟩) bit = inactive (16*0+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_0
end AspisR1.CuSavingsS2Tables
