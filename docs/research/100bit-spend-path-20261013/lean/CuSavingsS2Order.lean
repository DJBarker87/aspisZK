import CuSavingsS2TableData

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
def firstPositions : List Nat := [0,1,2,3,4,5,7,12,44,45,46,48]
def first (g : Fin 12) : Nat := firstPositions.getD g.val 0

theorem masks_distinct : masks.Nodup := by decide

theorem first_lt (g : Fin 12) : first g < 64 := by
  fin_cases g <;> decide

theorem first_occurrence (g : Fin 12) :
    groupValue ⟨first g,first_lt g⟩ = g.val ∧
      ∀ j : Fin 64, j.val < first g → groupValue j ≠ g.val := by
  fin_cases g <;> decide

theorem first_order (g h : Fin 12) (hgh : g.val < h.val) : first g < first h := by
  fin_cases g <;> fin_cases h <;> simp_all [first,firstPositions]

#print axioms masks_distinct
#print axioms first_lt
#print axioms first_occurrence
#print axioms first_order
end AspisR1.CuSavingsS2Tables
