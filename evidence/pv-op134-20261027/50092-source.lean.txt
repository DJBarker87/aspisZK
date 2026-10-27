import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows06
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [571#u16, 572#u16, 576#u16, 587#u16, 588#u16, 592#u16, 603#u16, 604#u16, 608#u16, 619#u16, 620#u16, 624#u16, 635#u16, 636#u16, 640#u16, 651#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 571 ≤ r.val ∧ r.val ≤ 651 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows06
