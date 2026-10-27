import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows09
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [827#u16, 828#u16, 832#u16, 843#u16, 844#u16, 848#u16, 860#u16, 864#u16, 875#u16, 876#u16, 880#u16, 891#u16, 892#u16, 896#u16, 908#u16, 913#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 827 ≤ r.val ∧ r.val ≤ 913 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows09
