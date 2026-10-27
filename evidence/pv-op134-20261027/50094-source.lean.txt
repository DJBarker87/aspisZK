import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows08
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [736#u16, 747#u16, 748#u16, 752#u16, 763#u16, 764#u16, 768#u16, 779#u16, 780#u16, 784#u16, 795#u16, 796#u16, 800#u16, 811#u16, 812#u16, 816#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 736 ≤ r.val ∧ r.val ≤ 816 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows08
