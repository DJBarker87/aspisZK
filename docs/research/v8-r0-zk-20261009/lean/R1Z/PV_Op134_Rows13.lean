import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows13
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [1010#u16, 1012#u16, 1014#u16, 1015#u16, 1017#u16, 1018#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 1010 ≤ r.val ∧ r.val ≤ 1018 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 6 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows13
