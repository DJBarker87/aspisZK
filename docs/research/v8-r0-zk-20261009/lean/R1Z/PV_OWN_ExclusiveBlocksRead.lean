import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem ExclusiveBlocksRead (m : Memory) (l : Loan) (slot : Nat) (c : Cell) (hx:l.exclusive=true) :
 ¬Readable (borrow l m) slot l.token c := by
 intro h
 have hf:=h.2 l List.mem_cons_self rfl
 rw [hx] at hf
 cases hf
#print axioms ExclusiveBlocksRead
end R1Z.PV_OWN_Laws
