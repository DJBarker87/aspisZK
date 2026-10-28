import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem BoxInitialized (k : Codec T) (m : Memory) (o : Nat) (t : Token) (v : T) (h:BoxView k m o t v) :
 View k m t 0 v := by
 obtain ⟨c,a,_,_,b⟩:=h
 exact ⟨c,a.1,b⟩
#print axioms BoxInitialized
end R1Z.PV_OWN_Laws
