import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem InitLive (k : Codec T) (t : Token) (c : Cell) (s : Nat) (v : T) (m : Memory)
 (h:Live m t c) : Live (initialize k t c s v m) t (store c s k.width (k.encode v)) := by
 exact ⟨put_same _ _ _,h.2.1,h.2.2⟩
#print axioms InitLive
end R1Z.PV_OWN_Laws
