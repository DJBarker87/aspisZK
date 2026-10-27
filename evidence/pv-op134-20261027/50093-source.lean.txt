import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows07
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [652#u16, 656#u16, 667#u16, 668#u16, 672#u16, 683#u16, 684#u16, 688#u16, 699#u16, 700#u16, 704#u16, 715#u16, 716#u16, 720#u16, 731#u16, 732#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 652 ≤ r.val ∧ r.val ≤ 732 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows07
