import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem TakeIdempotent (m : Memory) (s : Nat) : take s (take s m)=take s m := by
 cases m; simp only [take]; congr; funext i; by_cases h:i=s <;> simp [h]
#print axioms TakeIdempotent
end R1Z.PV_OWN_Laws
