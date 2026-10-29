import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem ReadUnique (k : Codec T) (m : Memory) (t : Token) (s : Nat) (a b : T)
 (ha:View k m t s a) (hb:View k m t s b) : a=b := by
 obtain ⟨ca,la,ra⟩:=ha
 obtain ⟨cb,lb,rb⟩:=hb
 have eq : ca=cb := Option.some.inj (la.1.symm.trans lb.1)
 subst cb
 exact unique k ca s a b ra rb
#print axioms ReadUnique
end R1Z.PV_OWN_Laws
