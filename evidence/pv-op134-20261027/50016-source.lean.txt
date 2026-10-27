import R1Z.PV_CBM_CellChunk07
import R1Z.PV_Op134_Order
namespace R1Z.PV_Op134_CellOrder07
open PV_Op134_Order
set_option autoImplicit false
theorem sorted : increasing PV_CBM_CellChunk07.literals := by
  unfold increasing
  decide
-- Small literal block checks; no recurrence or finite-field arithmetic unfolds.
theorem bounds : ∀ c ∈ PV_CBM_CellChunk07.literals,
    2078 ≤ key c ∧ key c ≤ 2414 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
  simp only [PV_CBM_CellChunk07.literals, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  intro c h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst c <;> decide
#print axioms sorted
#print axioms bounds
end R1Z.PV_Op134_CellOrder07
