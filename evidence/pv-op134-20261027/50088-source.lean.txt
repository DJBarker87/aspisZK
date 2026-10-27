import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows02
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [187#u16, 188#u16, 192#u16, 203#u16, 204#u16, 208#u16, 219#u16, 220#u16, 224#u16, 235#u16, 236#u16, 240#u16, 251#u16, 252#u16, 256#u16, 267#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 187 ≤ r.val ∧ r.val ≤ 267 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows02
