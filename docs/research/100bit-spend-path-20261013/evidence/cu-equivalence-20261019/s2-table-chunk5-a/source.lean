import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem block_33 (bit : Fin 16) :
    row (16*33+bit.val) < 1024 ∧
      groupMask (group ⟨33,by decide⟩) bit = inactive (16*33+bit.val) := by
  fin_cases bit <;> decide

theorem block_34 (bit : Fin 16) :
    row (16*34+bit.val) < 1024 ∧
      groupMask (group ⟨34,by decide⟩) bit = inactive (16*34+bit.val) := by
  fin_cases bit <;> decide

theorem block_35 (bit : Fin 16) :
    row (16*35+bit.val) < 1024 ∧
      groupMask (group ⟨35,by decide⟩) bit = inactive (16*35+bit.val) := by
  fin_cases bit <;> decide

theorem block_36 (bit : Fin 16) :
    row (16*36+bit.val) < 1024 ∧
      groupMask (group ⟨36,by decide⟩) bit = inactive (16*36+bit.val) := by
  fin_cases bit <;> decide

theorem block_37 (bit : Fin 16) :
    row (16*37+bit.val) < 1024 ∧
      groupMask (group ⟨37,by decide⟩) bit = inactive (16*37+bit.val) := by
  fin_cases bit <;> decide

theorem block_38 (bit : Fin 16) :
    row (16*38+bit.val) < 1024 ∧
      groupMask (group ⟨38,by decide⟩) bit = inactive (16*38+bit.val) := by
  fin_cases bit <;> decide

theorem block_39 (bit : Fin 16) :
    row (16*39+bit.val) < 1024 ∧
      groupMask (group ⟨39,by decide⟩) bit = inactive (16*39+bit.val) := by
  fin_cases bit <;> decide

theorem block_40 (bit : Fin 16) :
    row (16*40+bit.val) < 1024 ∧
      groupMask (group ⟨40,by decide⟩) bit = inactive (16*40+bit.val) := by
  fin_cases bit <;> decide

#print axioms block_33
#print axioms block_34
#print axioms block_35
#print axioms block_36
#print axioms block_37
#print axioms block_38
#print axioms block_39
#print axioms block_40
end AspisR1.CuSavingsS2Tables
