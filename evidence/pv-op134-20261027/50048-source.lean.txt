import R1Z.PV_CBM_CellChunk27
import R1Z.PV_Op134_Order
namespace R1Z.PV_Op134_CellOrder27
open PV_Op134_Order
set_option autoImplicit false
theorem sorted : increasing PV_CBM_CellChunk27.literals := by
  unfold increasing
  decide
-- Small literal block checks; no recurrence or finite-field arithmetic unfolds.
theorem bounds : ∀ c ∈ PV_CBM_CellChunk27.literals,
    8061 ≤ key c ∧ key c ≤ 8222 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
  simp only [PV_CBM_CellChunk27.literals, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  intro c h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst c <;> decide
#print axioms sorted
#print axioms bounds
end R1Z.PV_Op134_CellOrder27
