import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows05
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [460#u16, 464#u16, 475#u16, 491#u16, 496#u16, 507#u16, 508#u16, 512#u16, 523#u16, 528#u16, 539#u16, 540#u16, 544#u16, 555#u16, 556#u16, 560#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 460 ≤ r.val ∧ r.val ≤ 560 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows05
