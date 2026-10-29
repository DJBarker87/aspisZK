import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem SharedRead (m : Memory) (l : Loan) (slot : Nat) (t : Token) (c : Cell)
 (h:Readable m slot t c) (shared:l.exclusive=false) : Readable (borrow l m) slot t c := by
 refine ⟨h.1,?_⟩
 intro q hq ht
 cases List.mem_cons.mp hq with
 | inl eq => subst q; exact shared
 | inr hm => exact h.2 q hm ht
#print axioms SharedRead
end R1Z.PV_OWN_Laws
