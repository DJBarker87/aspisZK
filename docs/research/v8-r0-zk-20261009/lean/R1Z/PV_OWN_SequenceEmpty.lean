import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem SequenceEmpty (w : State S X) : (sequence (E:=E) [] w).calls=[] ∧
 (sequence (E:=E) [] w).world=w ∧ (sequence (E:=E) [] w).outcome=.ok () := ⟨rfl,rfl,rfl⟩
#print axioms SequenceEmpty
end R1Z.PV_OWN_Laws
