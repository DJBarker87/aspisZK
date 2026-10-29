import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem VecCell (k : Codec T) (m : Memory) (v : Vector T) (h:VecView k m v) :
 ∃ c, Owned m v.owner v.token c ∧ c.size=v.capacity*k.width := by
 obtain ⟨c,a,b,_⟩:=h
 exact ⟨c,a,b⟩
#print axioms VecCell
end R1Z.PV_OWN_Laws
