import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows01
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [96#u16, 107#u16, 108#u16, 112#u16, 123#u16, 124#u16, 128#u16, 139#u16, 140#u16, 144#u16, 155#u16, 156#u16, 160#u16, 171#u16, 172#u16, 176#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 96 ≤ r.val ∧ r.val ≤ 176 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows01
