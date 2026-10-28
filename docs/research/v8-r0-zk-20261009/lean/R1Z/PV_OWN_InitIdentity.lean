import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem InitIdentity (k : Codec T) (t : Token) (c : Cell) (s : Nat) (v : T) (m : Memory) :
 (initialize k t c s v m).generations=m.generations ∧
 (initialize k t c s v m).slots=m.slots ∧ (initialize k t c s v m).loans=m.loans := ⟨rfl,rfl,rfl⟩
#print axioms InitIdentity
end R1Z.PV_OWN_Laws
