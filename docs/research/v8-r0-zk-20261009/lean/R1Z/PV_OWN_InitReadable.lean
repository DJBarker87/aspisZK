import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem InitReadable (k : Codec T) (t : Token) (c : Cell) (slot s : Nat) (v : T) (m : Memory)
 (h:Readable m slot t c) : Readable (initialize k t c s v m) slot (store c s k.width (k.encode v)) := by
 exact ⟨⟨⟨put_same _ _ _,h.1.1.2.1,h.1.1.2.2⟩,h.1.2.1,h.1.2.2⟩,h.2⟩
#print axioms InitReadable
end R1Z.PV_OWN_Laws
