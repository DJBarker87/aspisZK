import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows10
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [914#u16, 917#u16, 918#u16, 921#u16, 922#u16, 925#u16, 926#u16, 929#u16, 930#u16, 933#u16, 934#u16, 937#u16, 938#u16, 941#u16, 942#u16, 945#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 914 ≤ r.val ∧ r.val ≤ 945 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows10
