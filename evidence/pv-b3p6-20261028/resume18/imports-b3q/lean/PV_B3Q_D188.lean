import PV_B3P_D188Link14227
namespace PV_B3Q_D188
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Direct indexed assignment used by the owned copy and terminal emissions. -/
def direct_store (n : Usize) (xs : Array Q14 n) (index : Usize) (value : Q14) : Result (Array Q14 n) :=
  Array.update xs index value
/-- Both indexed assignment and an explicit restored mutable borrow discharge
exactly the standing D188 store predicate, with no strengthened domain. -/
theorem direct_store_link : PV_B3P_Link_D188 direct_store := by
  intro n xs index value _
  rfl
theorem borrow_and_direct (n : Usize) (xs : Array Q14 n) (index : Usize)
    (value : Q14) (bound : index.val < n.val) :
    borrowed_store14 n xs index value = direct_store n xs index value :=
  borrowed_store_binding14 n xs index value bound
/-- Any later caller sees the restored array, including on fail/div continuations. -/
theorem caller_restoration {α : Type} (next : Array Q14 16#usize → Result α)
    (xs : Array Q14 16#usize) (index : Usize) (value : Q14)
    (bound : index.val < 16) :
    (borrowed_store14 16#usize xs index value >>= next) =
      (direct_store 16#usize xs index value >>= next) := by
  rw [borrow_and_direct _ xs index value bound]
#print axioms direct_store_link
#print axioms borrow_and_direct
#print axioms caller_restoration
end PV_B3Q_D188
