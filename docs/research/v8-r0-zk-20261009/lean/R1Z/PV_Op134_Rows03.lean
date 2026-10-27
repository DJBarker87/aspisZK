import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows03
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [268#u16, 272#u16, 283#u16, 284#u16, 288#u16, 299#u16, 300#u16, 304#u16, 315#u16, 316#u16, 320#u16, 331#u16, 332#u16, 336#u16, 347#u16, 348#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 268 ≤ r.val ∧ r.val ≤ 348 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows03
