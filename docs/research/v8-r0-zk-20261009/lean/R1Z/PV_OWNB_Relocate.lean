import R1Z.PV_OWNB_WriteProducer
import R1Z.PV_OWNB_WriteConsumer
set_option autoImplicit false
namespace R1Z.PV_OWNB_Relocate
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_Link PV_OWNB_LinkCodec
/-- The two deployed endpoint assignments preserve kind and pad bytes. -/
def cell (c : Cell) (s : Nat) (p q : UInt16) : Cell :=
 store (store c s 2 (PV_OWN_U16.encode p)) (s+2) 2 (PV_OWN_U16.encode q)

theorem write (c : Cell) (s : Nat) (v : Link) (p q : UInt16) (h:NativeView c s v) :
 NativeView (cell c s p q) s (relocate v p q) := by
 exact PV_OWNB_WriteConsumer.write _ _ _ q (PV_OWNB_WriteProducer.write c s v p h)

theorem pad (c : Cell) (s : Nat) (p q : UInt16) (i : Nat) (hi:4≤i) :
 (cell c s p q).contents (s+i)=c.contents (s+i) := by
 unfold cell store
 rw [outside _ _ _ _ _ (by right; omega)]
 rw [outside _ _ _ _ _ (by right; omega)]
#print axioms write
#print axioms pad
end R1Z.PV_OWNB_Relocate
