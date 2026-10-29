import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem BorrowBlocksWrite (m : Memory) (l : Loan) (slot : Nat) (c : Cell) :
 ¬Writable (borrow l m) slot l.token c := by
 intro h
 exact h.2 l (List.mem_cons_self) rfl
#print axioms BorrowBlocksWrite
end R1Z.PV_OWN_Laws
