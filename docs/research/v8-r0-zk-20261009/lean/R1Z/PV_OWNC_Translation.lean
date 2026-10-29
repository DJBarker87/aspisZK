import R1Z.PV_OWNB_Relocate
import R1Z.PV_OWNC_LinkPush
set_option autoImplicit false
namespace R1Z.PV_OWNC_Translation
open PV_OWN_Link PV_OWN_Heap PV_OWN_Bytes PV_OWNB_LinkCodec
/-- Preserve the two separate conditional stores in deployed forest source. -/
def producer (v : Link) : UInt16 := if v.producer.toNat≥864 then v.producer+48 else v.producer
def consumer (v : Link) : UInt16 := if v.consumer.toNat≥864 then v.consumer+48 else v.consumer
def first (c : Cell) (s : Nat) (v : Link) : Cell :=
 if v.producer.toNat≥864 then store c s 2 (PV_OWN_U16.encode (v.producer+48)) else c
def second (c : Cell) (s : Nat) (v : Link) : Cell :=
 if v.consumer.toNat≥864 then store c (s+2) 2 (PV_OWN_U16.encode (v.consumer+48)) else c

theorem producer_store (c : Cell) (s : Nat) (v : Link) (h:NativeView c s v) :
 NativeView (first c s v) s {v with producer:=producer v} := by
 unfold first producer
 split
 · exact PV_OWNB_WriteProducer.write c s v _ h
 · exact h

theorem consumer_store (c : Cell) (s : Nat) (v : Link) (h:NativeView c s v) :
 NativeView (second c s v) s {v with consumer:=consumer v} := by
 unfold second consumer
 split
 · exact PV_OWNB_WriteConsumer.write c s v _ h
 · exact h

theorem both (c : Cell) (s : Nat) (v : Link) (h:NativeView c s v) :
 NativeView (second (first c s v) s v) s (relocate v (producer v) (consumer v)) := by
 exact consumer_store _ s {v with producer:=producer v} (producer_store c s v h)
#print axioms producer_store
#print axioms consumer_store
#print axioms both
end R1Z.PV_OWNC_Translation
