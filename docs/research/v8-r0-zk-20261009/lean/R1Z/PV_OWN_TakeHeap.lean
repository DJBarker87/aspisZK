import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem TakeHeap (m : Memory) (s : Nat) : (take s m).heap=m.heap ∧
 (take s m).generations=m.generations ∧ (take s m).loans=m.loans := ⟨rfl,rfl,rfl⟩
#print axioms TakeHeap
end R1Z.PV_OWN_Laws
