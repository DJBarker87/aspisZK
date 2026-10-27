import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows04
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [352#u16, 363#u16, 364#u16, 368#u16, 379#u16, 380#u16, 384#u16, 395#u16, 396#u16, 411#u16, 412#u16, 416#u16, 428#u16, 443#u16, 448#u16, 459#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 352 ≤ r.val ∧ r.val ≤ 459 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows04
