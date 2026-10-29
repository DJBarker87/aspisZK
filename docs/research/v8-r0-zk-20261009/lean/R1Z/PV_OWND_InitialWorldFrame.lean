import R1Z.PV_OWND_InitialRun
import R1Z.PV_OWND_PaddedFrame
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialWorldFrame
open PV_OWN_Operations PV_OWN_Link PV_OWN_Heap PV_OWN_Bytes PV_W_Threading PV_OWND_InitialRun

theorem retained {S X E : Type} (t : Token) (owner : Nat)
 (payload : Nat → Link → Bytes) (w : State S X) :
 (stores (E:=E) t owner payload w).world.allocator=w.allocator ∧
 (stores (E:=E) t owner payload w).world.extra=w.extra ∧
 (stores (E:=E) t owner payload w).calls=[] := ⟨rfl,rfl,rfl⟩

theorem heap_frame {S X E : Type} (t : Token) (owner : Nat)
 (payload : Nat → Link → Bytes) (w : State S X) (address : Nat) (hne:address≠t.address) :
 (stores (E:=E) t owner payload w).world.memory.heap address=w.memory.heap address := by
 exact PV_OWND_PaddedFrame.other _ _ _ _ _ address hne
#print axioms retained
#print axioms heap_frame
end R1Z.PV_OWND_InitialWorldFrame
