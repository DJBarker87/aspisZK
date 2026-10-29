import PV_B3P_ArrayWrite227
namespace PV_B3P_Groups14227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev Q14 := aspis_core.field.QM31
abbrev Store14 := (n : Usize) → Array Q14 n → Usize → Q14 → Result (Array Q14 n)
def borrowed_store14 (n : Usize) (xs : Array Q14 n) (index : Usize) (value : Q14) : Result (Array Q14 n) := do
  let (_,back) ← Array.index_mut_usize xs index
  .ok (back value)
/-- D188 store/restore law for arbitrary array contents, including every caller
state. Associating each source call site with this port is still required. -/
def PV_B3P_Link_D188 (store : Store14) : Prop :=
  ∀ n xs index value, index.val < n.val →
    store n xs index value = Array.update xs index value

theorem borrowed_store_binding14 : PV_B3P_Link_D188 borrowed_store14 := by
  intro n xs index value bound
  unfold borrowed_store14
  rw [PV_B3P_ArrayWrite227.borrow xs index bound,
    PV_B3P_ArrayWrite227.update xs index bound]
  rfl

theorem D188_readback14 (store : Store14) (binding : PV_B3P_Link_D188 store)
    (n : Usize) (xs : Array Q14 n) (index : Usize) (value : Q14) (bound : index.val < n.val) :
    (do let written ← store n xs index value; Array.index_usize written index) = .ok value := by
  rw [binding n xs index value bound,PV_B3P_ArrayWrite227.update xs index bound]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value _ index (by simp only [Aeneas.Std.Array.set,List.length_set]; exact bound)]
  exact congrArg Result.ok (PV_B3P_ArrayWrite227.restored_value xs index bound value)
#print axioms borrowed_store_binding14
#print axioms D188_readback14
end PV_B3P_Groups14227
