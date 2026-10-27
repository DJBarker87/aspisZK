import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows12
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [978#u16, 981#u16, 982#u16, 985#u16, 986#u16, 989#u16, 990#u16, 993#u16, 994#u16, 997#u16, 998#u16, 1001#u16, 1002#u16, 1005#u16, 1006#u16, 1008#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 978 ≤ r.val ∧ r.val ≤ 1008 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows12
