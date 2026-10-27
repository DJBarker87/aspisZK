import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows11
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [946#u16, 949#u16, 950#u16, 953#u16, 954#u16, 957#u16, 958#u16, 961#u16, 962#u16, 965#u16, 966#u16, 969#u16, 970#u16, 973#u16, 974#u16, 977#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 946 ≤ r.val ∧ r.val ≤ 977 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows11
