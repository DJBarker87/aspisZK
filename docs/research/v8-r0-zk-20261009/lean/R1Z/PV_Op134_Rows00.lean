import R1Z.PV_CBM_PushList
namespace R1Z.PV_Op134_Rows00
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [11#u16, 12#u16, 27#u16, 28#u16, 32#u16, 43#u16, 44#u16, 48#u16, 59#u16, 60#u16, 64#u16, 75#u16, 76#u16, 80#u16, 91#u16, 92#u16]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, 11 ≤ r.val ∧ r.val ≤ 92 ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst r <;> decide
theorem length : rows.length = 16 := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.PV_Op134_Rows00
