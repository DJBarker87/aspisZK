import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem BorrowOwned (m : Memory) (l : Loan) (slot : Nat) (t : Token) (c : Cell)
 (h:Owned m slot t c) : Owned (borrow l m) slot t c := h
#print axioms BorrowOwned
end R1Z.PV_OWN_Laws
